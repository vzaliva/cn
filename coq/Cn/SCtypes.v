Require Import Coq.Structures.DecidableType.
Require Import Coq.Structures.DecidableTypeEx.
Require Import Coq.Program.Equality.
Require Import Cerberus.Symbol.
Require Import Cerberus.IntegerType.
Require Import Cerberus.Ctype.
Require Import Sym.
(* Qualifiers *)
Definition qualifiers := Ctype.qualifiers.

(* C types *)
Inductive ctype : Type :=
  | Void : ctype
  | Integer : integerType -> ctype
  | Array : ctype * option nat -> ctype
  | Pointer : ctype -> ctype
  | Struct : sym -> ctype
  | SCFunction : (qualifiers * ctype) * (list (ctype * bool)) * bool -> ctype.

Definition t := ctype.

Inductive is_struct : t -> Prop :=
  | is_struct_struct : forall s, is_struct (Struct s).

Inductive is_function : t -> Prop :=
  | is_function_function : forall q args ret, is_function (SCFunction (q, args, ret)).


(* C concrete signature *)
Record c_concrete_sig := mk_c_concrete_sig {
  sig_return_ty : Ctype.ctype;
  sig_arg_tys : list Ctype.ctype;
  sig_variadic : bool;
  sig_has_proto : bool
}.

Module IntegerBaseType_as_MiniDecidableType <: MiniDecidableType.
  Definition t := integerBaseType.
  Definition eq := @eq t.
  Lemma eq_dec : forall (x y : t), { eq x y } + { ~ eq x y }.
  Proof.
    unfold eq.
    intros x y.
    destruct x, y.
    all: try (right; discriminate).
    all: try (left; reflexivity).
    all: decide equality.
    all: apply Nat_as_DT.eq_dec.
  Qed.
End IntegerBaseType_as_MiniDecidableType.

Module IntegerType_as_MiniDecidableType <: MiniDecidableType.
  Definition t := integerType.
  Definition eq := @eq t.
  Lemma eq_dec : forall (x y : t), { eq x y } + { ~ eq x y }.
  Proof.
    unfold eq.
    intros x y.
    destruct x, y.
    all: try (right; discriminate).
    all: try (left; reflexivity).
    all: decide equality.
    all: try apply IntegerBaseType_as_MiniDecidableType.eq_dec.
    all: try apply Sym_t_as_MiniDecidableType.eq_dec.
  Qed.
End IntegerType_as_MiniDecidableType.

Module qualifiers_as_MiniDecidableType <: MiniDecidableType.
  Definition t := qualifiers.
  Definition eq := @eq t.
  Lemma eq_dec : forall (x y : t), { eq x y } + { ~ eq x y }.
  Proof.
    unfold eq.
    intros x y.
    destruct x, y.
    do 2 decide equality.
  Qed.
End qualifiers_as_MiniDecidableType.

Module SCtypes_as_MiniDecidableType <: MiniDecidableType.
  Definition t := t.
  Definition eq := @eq t.
  Lemma eq_dec : forall (x y : t), { eq x y } + { ~ eq x y }.
  Proof.
    admit.
  Admitted.
End SCtypes_as_MiniDecidableType.
