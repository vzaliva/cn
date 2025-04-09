module IT = IndexTerms
module LC = LogicalConstraints
module Req = Request
open Typing

let debug_constraint_failure_diagnostics
      lvl
      (model_with_q : Solver.model_with_q)
      simp_ctxt
      c
  =
  let model = fst model_with_q in
  if !Pp.print_level == 0 then
    ()
  else (
    let pp_f = IT.pp_with_eval (Solver.eval model) in
    let diag msg c =
      match (c, model_with_q) with
      | LC.T tm, _ ->
        Pp.debug lvl (lazy (Pp.item msg (IT.pp tm)));
        Pp.debug lvl (lazy (pp_f tm))
      | LC.Forall ((sym, _bt), tm), (_, [ (sym', _bt') ]) ->
        let tm' = IT.subst (IT.make_rename ~from:sym ~to_:sym') tm in
        Pp.debug lvl (lazy (Pp.item ("quantified " ^ msg) (IT.pp tm)));
        Pp.debug lvl (lazy (pp_f tm'))
      | _ ->
        Pp.warn
          (Locations.other __LOC__)
          (Pp.bold "unexpected quantifier count with model")
    in
    diag "counterexample, expanding" c;
    let c2 = Simplify.LogicalConstraints.simp simp_ctxt c in
    if LC.equal c c2 then
      ()
    else
      diag "simplified variant" c2)


module General = struct
  type one =
    { one_index : IT.t;
      value : IT.t
    }

  type many =
    { many_guard : IT.t;
      value : IT.t
    }

  type uiinfo = Error_common.situation * TypeErrors.RequestChain.t

  type case =
    | One of one
    | Many of many

  type cases = C of case list

  let add_case case (C cases) = C (cases @ [ case ])

  let cases_to_map loc (situation, requests) a_bt item_bt (C cases) =
    let here = Locations.other __LOC__ in
    let update_with_ones base_array ones =
      List.fold_left
        (fun m { one_index; value } -> IT.map_set_ m (one_index, value) here)
        base_array
        ones
    in
    let ones, manys =
      List.partition_map (function One c -> Left c | Many c -> Right c) cases
    in
    let@ base_value =
      let module BT = BaseTypes in
      match (manys, item_bt) with
      | [ { many_guard = _; value } ], _ -> return value
      | [], _ | _, BT.Unit -> return (IT.default_ (BT.Map (a_bt, item_bt)) here)
      | _many, _ ->
        let term = IT.bool_ true here in
        let@ model = model_with here term in
        let model = Option.get model in
        let msg ctxt =
          TypeErrors.Merging_multiple_arrays { requests; situation; ctxt; model }
        in
        fail (fun ctxt -> { loc; msg = msg ctxt })
    in
    return (update_with_ones base_value ones)


  (* this version is parametric in resource_request (defined below) to ensure the
     return-type (also parametric) is as general as possible *)
  let parametric_ftyp_args_request_step
        resource_request
        rt_subst
        loc
        (uiinfo : uiinfo)
        _original_resources
        ftyp
        changed_or_deleted
    =
    (* take one step of the "spine" judgement, reducing a function-type by claiming an
       argument resource or otherwise reducing towards an instantiated return-type *)
    let@ simp_ctxt = simp_ctxt () in
    let module LAT = LogicalArgumentTypes in
    match ftyp with
    | LAT.Resource ((s, (resource, _bt)), info, ftyp) ->
      let resource = Simplify.Request.simp simp_ctxt resource in
      let situation, request_chain = uiinfo in
      let step =
        TypeErrors.RequestChain.
          { resource; loc = Some (fst info); reason = Some ("arg " ^ Sym.pp_string s) }
      in
      let request_chain = step :: request_chain in
      let uiinfo = (situation, request_chain) in
      let@ o_re_oarg = resource_request loc uiinfo resource in
      (match o_re_oarg with
       | None ->
         let here = Locations.other __LOC__ in
         let@ model = model_with loc (IT.bool_ true here) in
         let model = Option.get model in
         fail (fun ctxt ->
           (* let ctxt = { ctxt with resources = original_resources } in *)
           let msg =
             TypeErrors.Missing_resource
               { requests = request_chain; situation; model; ctxt }
           in
           { loc; msg })
       | Some ((re, Resource.O oargs), changed_or_deleted', l) ->
         assert (Request.equal re resource);
         let oargs = Simplify.IndexTerms.simp simp_ctxt oargs in
         let changed_or_deleted = changed_or_deleted @ changed_or_deleted' in
         return
           (LAT.subst rt_subst (IT.make_subst [ (s, oargs) ]) ftyp, changed_or_deleted, l))
    | Define ((s, it), _info, ftyp) ->
      let it = Simplify.IndexTerms.simp simp_ctxt it in
      return (LAT.subst rt_subst (IT.make_subst [ (s, it) ]) ftyp, changed_or_deleted, [])
    | Constraint (c, info, ftyp) ->
      let@ provable = provable loc in
      Pp.(debug 9 (lazy (item "checking constraint" (LC.pp c))));
      let res = provable c in
      (match res with
       | `True -> return (ftyp, changed_or_deleted, [])
       | `False ->
         let@ model = model () in
         let@ all_cs = get_cs () in
         let () = assert (not (LC.Set.mem c all_cs)) in
         debug_constraint_failure_diagnostics 6 model simp_ctxt c;
         let@ () = Diagnostics.investigate model c in
         fail (fun ctxt ->
           (* let ctxt = { ctxt with resources = original_resources } in *)
           { loc;
             msg =
               TypeErrors.Unproven_constraint
                 { constr = c; info; requests = snd uiinfo; ctxt; model }
           }))
    | I _rt -> return (ftyp, changed_or_deleted, [])


  (* TODO: check that oargs are in the same order? *)
  let rec predicate_request loc (uiinfo : uiinfo) (requested : Req.Predicate.t)
    : (Resource.predicate * int list * Prooflog.log) option m
    =
    Pp.(debug 7 (lazy (item __LOC__ (Req.pp (P requested)))));
    let start_timing = Pp.time_log_start __LOC__ "" in
    let@ oarg_bt = WellTyped.oarg_bt_of_pred loc requested.name in
    let@ provable = provable loc in
    let@ global = get_global () in
    let@ simp_ctxt = simp_ctxt () in
    let resource_scan re ((needed : bool), oargs) =
      let continue = (Unchanged, (needed, oargs)) in
      if not needed then
        continue
      else (
        match re with
        | Req.P p', p'_oarg when Req.subsumed requested.name p'.name ->
          let here = Locations.other __LOC__ in
          let addr_iargs_eqs =
            IT.(eq_ ((addr_ requested.pointer) here, addr_ p'.pointer here) here)
            :: List.map2 (fun x y -> IT.eq__ x y here) requested.iargs p'.iargs
          in
          let addr_iargs_match = IT.and_ addr_iargs_eqs here in
          let alloc_id_eq =
            IT.(eq_ (allocId_ requested.pointer here, allocId_ p'.pointer here) here)
          in
          let debug_failure model msg term =
            Pp.debug 9 (lazy (Pp.item msg (Req.pp (fst re))));
            debug_constraint_failure_diagnostics 9 model simp_ctxt (LC.T term)
          in
          (match provable (LC.T addr_iargs_match) with
           | `True ->
             (match provable (LC.T alloc_id_eq) with
              | `True ->
                Pp.debug 9 (lazy (Pp.item "used resource" (Req.pp (fst re))));
                (Deleted, (false, p'_oarg))
              | `False ->
                debug_failure
                  (Solver.model ())
                  "couldn't use resource (matched address but not provenance)"
                  alloc_id_eq;
                continue)
           | `False ->
             let model = Solver.model () in
             (match provable (LC.T alloc_id_eq) with
              | `True ->
                debug_failure
                  model
                  "couldn't use resource (matched provenance but not address)"
                  addr_iargs_match;
                continue
              | `False ->
                let patched =
                  IT.eq_ (requested.pointer, p'.pointer) here :: List.tl addr_iargs_eqs
                in
                debug_failure
                  (Solver.model ())
                  "couldn't use resource"
                  IT.(and_ patched here);
                continue))
        | _re -> continue)
    in
    let needed = true in
    let here = Locations.other __LOC__ in
    let@ (needed, oarg), changed_or_deleted =
      map_and_fold_resources loc resource_scan (needed, O (IT.default_ oarg_bt here))
    in
    let not_str = lazy Pp.(if needed then !^" not " else !^" ") in
    Pp.(debug 9 (Lazy.map (fun x -> !^"resource was" ^^ x ^^ !^"found") not_str));
    let@ res =
      match needed with
      | false -> return (Some ((requested, oarg), changed_or_deleted, []))
      | true ->
        (match Pack.packing_ft here global provable (P requested) with
         | Some packing_ft ->
           let ft_pp =
             lazy (LogicalArgumentTypes.pp (fun _ -> Pp.string "resource") packing_ft)
           in
           Pp.debug 9 (Lazy.map (Pp.item "attempting to pack compound resource") ft_pp);
           let@ o, changed_or_deleted, log =
             ftyp_args_request_for_pack loc uiinfo packing_ft
           in
           return (Some ((requested, Resource.O o), changed_or_deleted, log))
         | None ->
           let req_pp = lazy (Req.pp (P requested)) in
           Pp.debug 9 (Lazy.map (Pp.item "no pack rule for resource, failing") req_pp);
           return None)
    in
    Pp.time_log_end start_timing;
    return res


  and qpredicate_request_aux loc uiinfo (requested : Req.QPredicate.t) =
    Pp.(debug 7 (lazy (item __LOC__ (Req.pp (Q requested)))));
    let@ provable = provable loc in
    let@ simp_ctxt = simp_ctxt () in
    let needed = requested.permission in
    let step = requested.step in
    let@ (needed, oarg), rw_time =
      map_and_fold_resources
        loc
        (fun re (needed, oarg) ->
           let continue = (Unchanged, (needed, oarg)) in
           if IT.is_false needed then
             continue
           else (
             match re with
             | Q p', O p'_oarg
               when Req.subsumed requested.name p'.name
                    && Sctypes.equal step p'.step
                    && BaseTypes.equal (snd requested.q) (snd p'.q) ->
               let p' = Req.QPredicate.alpha_rename_ (fst requested.q) p' in
               let here = Locations.other __LOC__ in
               let pmatch =
                 (* Work-around for https://github.com/Z3Prover/z3/issues/7352 *)
                 Simplify.IndexTerms.simp simp_ctxt
                 @@ IT.eq_ (requested.pointer, p'.pointer) here
               in
               let iarg_match =
                 let eq_here x y = IT.eq_ (x, y) here in
                 IT.and_ (List.map2 eq_here requested.iargs p'.iargs) here
               in
               let took =
                 IT.and_ [ iarg_match; requested.permission; p'.permission ] here
               in
               (match provable (LC.Forall (requested.q, IT.not_ took here)) with
                | `True -> continue
                | `False ->
                  (match provable (LC.T pmatch) with
                   | `True ->
                     Pp.debug 9 (lazy (Pp.item "used resource" (Req.pp (fst re))));
                     let open IT in
                     let needed' =
                       [ needed; not_ (and_ [ iarg_match; p'.permission ] here) here ]
                     in
                     let permission' =
                       [ p'.permission; not_ (and_ [ iarg_match; needed ] here) here ]
                     in
                     let oarg =
                       add_case (Many { many_guard = took; value = p'_oarg }) oarg
                     in
                     ( Changed
                         (Q { p' with permission = and_ permission' here }, O p'_oarg),
                       (Simplify.IndexTerms.simp simp_ctxt (and_ needed' here), oarg) )
                   | `False ->
                     let model = Solver.model () in
                     Pp.debug
                       9
                       (lazy (Pp.item "couldn't use q-resource" (Req.pp (fst re))));
                     debug_constraint_failure_diagnostics 9 model simp_ctxt (LC.T pmatch);
                     continue))
             | _re -> continue))
        (needed, C [])
    in
    let here = Locations.other __LOC__ in
    let@ needed, oarg, l =
      let@ movable_indices = get_movable_indices () in
      let module Eff = Effectful.Make (Typing) in
      Eff.ListM.fold_rightM
        (fun (predicate_name, index) (needed, oarg, l) ->
           let continue = return (needed, oarg, l) in
           if
             (not (IT.is_false needed))
             && Req.subsumed requested.name predicate_name
             && BaseTypes.equal (snd requested.q) (IT.get_bt index)
           then (
             let su = IT.make_subst [ (fst requested.q, index) ] in
             let needed_at_index = IT.subst su needed in
             match provable (LC.T needed_at_index) with
             | `False -> continue
             | `True ->
               let@ c = get_typing_context () in
               let pointer =
                 IT.(arrayShift_ ~base:requested.pointer ~index requested.step here)
               in
               let sub_req : Req.Predicate.t =
                 { name = requested.name;
                   pointer;
                   iargs = List.map (IT.subst su) requested.iargs
                 }
               in
               let@ o_re_index = predicate_request loc uiinfo sub_req in
               (match o_re_index with
                | None -> continue
                | Some (((_p', O p'_oarg) as rr), _, l') ->
                  let oarg = add_case (One { one_index = index; value = p'_oarg }) oarg in
                  let sym, bt' = requested.q in
                  let needed' =
                    IT.(and_ [ needed; ne__ (sym_ (sym, bt', here)) index here ] here)
                  in
                  let@ c' = get_typing_context () in
                  let hints =
                    if Prooflog.is_enabled () then
                      Prooflog.PredicateRequest (c, fst uiinfo, sub_req, rr, l', c') :: l
                    else
                      []
                  in
                  return (needed', oarg, hints)))
           else
             continue)
        movable_indices
        (needed, oarg, [])
    in
    let nothing_more_needed = LC.forall_ requested.q (IT.not_ needed here) in
    Pp.debug 9 (lazy (Pp.item "checking resource remainder" (LC.pp nothing_more_needed)));
    let holds = provable nothing_more_needed in
    match holds with
    | `True -> return (Some (oarg, rw_time, l))
    | `False ->
      let@ model = model () in
      debug_constraint_failure_diagnostics 9 model simp_ctxt nothing_more_needed;
      return None


  and qpredicate_request loc uiinfo (requested : Req.QPredicate.t) =
    let@ o_oarg = qpredicate_request_aux loc uiinfo requested in
    let@ oarg_item_bt = WellTyped.oarg_bt_of_pred loc requested.name in
    match o_oarg with
    | None -> return None
    | Some (oarg, rw_time, l) ->
      let@ oarg = cases_to_map loc uiinfo (snd requested.q) oarg_item_bt oarg in
      let r =
        Req.QPredicate.
          { name = requested.name;
            pointer = requested.pointer;
            q = requested.q;
            q_loc = requested.q_loc;
            step = requested.step;
            permission = requested.permission;
            iargs = requested.iargs
          }
      in
      return (Some ((r, Resource.O oarg), rw_time, l))


  and ftyp_args_request_for_pack loc uiinfo ftyp =
    (* record the resources now, so errors are raised with all the resources present,
       rather than those that remain after some arguments are claimed *)
    let@ original_resources = all_resources_tagged loc in
    let rec loop ftyp rw_time l =
      match ftyp with
      | LogicalArgumentTypes.I rt -> return (rt, rw_time, l)
      | _ ->
        let@ ftyp, rw_time, l' =
          parametric_ftyp_args_request_step
            resource_request
            IT.subst
            loc
            uiinfo
            original_resources
            ftyp
            rw_time
        in
        loop ftyp rw_time (l @ l')
    in
    loop ftyp [] []


  and resource_request loc uiinfo (request : Req.t)
    : (Resource.t * int list * Prooflog.log) option m
    =
    match request with
    | P request ->
      let@ c = get_typing_context () in
      let@ result = predicate_request loc uiinfo request in
      let@ c' = get_typing_context () in
      return
        (Option.map
           (fun ((p, o), changed_or_deleted, l) ->
              let hints =
                if Prooflog.is_enabled () then
                  [ Prooflog.PredicateRequest (c, fst uiinfo, request, (p, o), l, c') ]
                else
                  []
              in
              ((Req.P p, o), changed_or_deleted, hints))
           result)
    | Q request ->
      let@ result = qpredicate_request loc uiinfo request in
      return
        (Option.map
           (fun ((q, o), changed_or_deleted, l) -> ((Req.Q q, o), changed_or_deleted, l))
           result)


  (* I don't know if we need the rw_time in check.ml? *)
  (*
     This is called directly from check.ml. Maybe it should be in Special, as
     predicate_request?
  *)
  let ftyp_args_request_step rt_subst loc situation original_resources ftyp =
    let@ rt, _rw_time, l =
      parametric_ftyp_args_request_step
        resource_request
        rt_subst
        loc
        situation
        original_resources
        ftyp
        []
    in
    (* We started with top-level call of ftyp_args_request_step, so we need to
       record the resource inference steps for the inner calls. They not nested
       under anything, so we need to record them separately. *)
    if Prooflog.is_enabled () then
      List.iter Prooflog.record_resource_inference_step l
    else
      ();
    return rt
end

module Special = struct
  let fail_missing_resource loc (situation, requests) =
    let here = Locations.other __LOC__ in
    let@ model = model_with loc (IT.bool_ true here) in
    let model = Option.get model in
    fail (fun ctxt ->
      let msg = TypeErrors.Missing_resource { requests; situation; model; ctxt } in
      { loc; msg })


  let predicate_request loc situation (request, oinfo) =
    let requests =
      [ TypeErrors.RequestChain.
          { resource = P request;
            loc = Option.map fst oinfo;
            reason = Option.map snd oinfo
          }
      ]
    in
    let uiinfo = (situation, requests) in
    let@ c = get_typing_context () in
    let@ result = General.predicate_request loc uiinfo request in
    match result with
    | Some (r, rw_time, log) ->
      let@ c' = get_typing_context () in
      if Prooflog.is_enabled () then
        Prooflog.record_resource_inference_step
          (Prooflog.PredicateRequest (c, fst uiinfo, request, r, log, c'))
      else
        ();
      return (r, rw_time)
    | None -> fail_missing_resource loc uiinfo


  let has_predicate loc situation (request, oinfo) =
    let@ result = sandbox @@ predicate_request loc situation (request, oinfo) in
    return (Result.is_ok result)


  (** This function checks whether [ptr1] belongs to a live allocation. It
      searches the context (without modification) for either an Alloc(p) or an
      Owned(p) such that (alloc_id) p == (alloc_id) ptr. *)
  let check_live_alloc reason loc ptr =
    let module Ans = struct
      type t =
        | Found
        | No_res
        | Model of (Solver.model_with_q * IT.t)
    end
    in
    let here = Locations.other __LOC__ in
    let alloc_id_matches found res_ptr =
      let@ found in
      match found with
      | Ans.Found -> return Ans.Found
      | No_res | Model _ ->
        let constr = IT.(eq_ (allocId_ ptr here, allocId_ res_ptr here) here) in
        let@ provable = provable loc in
        (match provable (LC.T constr) with
         | `True -> return Ans.Found
         | `False ->
           let@ model = model () in
           return (Ans.Model (model, constr)))
    in
    let f res found =
      let found =
        match res with
        | Req.Q _, _ -> found
        | Req.P { name = Owned _; pointer; iargs = _ }, _ ->
          alloc_id_matches found pointer
        | Req.P { name = PName name; pointer; iargs = _ }, _ ->
          if Sym.equal name Alloc.Predicate.sym then
            alloc_id_matches found pointer
          else
            found
      in
      (Unchanged, found)
    in
    let@ found, _ = map_and_fold_resources loc f (return Ans.No_res) in
    let@ found in
    match found with
    | Ans.Found -> return ()
    | No_res ->
      fail (fun ctxt ->
        let msg =
          TypeErrors.Allocation_not_live { reason; ptr; model_constr = None; ctxt }
        in
        { loc; msg })
    | Model (model, constr) ->
      fail (fun ctxt ->
        let msg =
          TypeErrors.Allocation_not_live
            { reason; ptr; model_constr = Some (model, constr); ctxt }
        in
        { loc; msg })


  let qpredicate_request loc situation (request, oinfo) =
    let requests =
      [ TypeErrors.RequestChain.
          { resource = Q request;
            loc = Option.map fst oinfo;
            reason = Option.map snd oinfo
          }
      ]
    in
    let uiinfo = (situation, requests) in
    let@ result = General.qpredicate_request loc uiinfo request in
    match result with
    | Some (r, rw_time, log) ->
      (* We started with top-level call of qpredicate_request, so we need to
         record the resource inference steps for the inner calls. They not
         nested under anything, so we need to record them separately. *)
      if Prooflog.is_enabled () then
        List.iter Prooflog.record_resource_inference_step log
      else
        ();
      return (r, rw_time)
    | None -> fail_missing_resource loc uiinfo
end
