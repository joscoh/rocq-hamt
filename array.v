Require Import Stdlib.ZArith.BinInt.
Require Import Stdlib.ZArith.Znat.
Require Import Stdlib.ZArith.BinIntDef.
Require Import Lia.

Require Import Stdlib.Lists.List.

Require Import Stdlib.Array.PArray.
Require Import Stdlib.Numbers.Cyclic.Int63.PrimInt63.

Require Import Stdlib.Logic.Eqdep_dec.

From Equations Require Import Equations.

Definition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.

Notation "x 'eqn' ':' p" := (exist _ x p) (only parsing, at level 20).

Definition cast {A1 A2: Type} (H: A1 = A2) (x: A1) : A2 :=
  match H with
  | eq_refl => x
  end.

Lemma bool_irrelevance (b : bool) (p1 p2 : b = true) : p1 = p2.
Proof.
  apply UIP_dec. apply Bool.bool_dec.
Qed.

(*Part 1: general lemmas about primitive int ops*)
Section PrimInt.

Definition int_to_nat (i: int) : nat :=
  Z.to_nat (Uint63.to_Z i).

Lemma uint63_not_zero_spec (i: int): Uint63.is_zero i = false <-> i <> 0%uint63.
Proof.
  destruct (Uint63.is_zero i) eqn : Hz; split; auto; try discriminate.
  - apply Uint63.is_zero_spec in Hz. subst; contradiction.
  - intros _ Hi. subst. assert (true = false); [|discriminate].
    rewrite <- (proj2 (Uint63.is_zero_spec 0)); auto.
Qed.

Lemma uint63_zero_iff (i: int): i = 0%uint63 <-> Uint63.to_Z i = 0%Z.
Proof.
  split; intros Hi; subst; auto.
  apply (f_equal Uint63.of_Z) in Hi.
  rewrite Uint63.of_to_Z in Hi. subst. auto.
Qed.

Lemma pred_to_z i (Hi: Uint63.is_zero i = false): (Uint63.to_Z (Uint63.pred i)) = (Uint63.to_Z i - 1)%Z.
Proof.
  rewrite Uint63.pred_spec.
  rewrite Z.mod_small; [ lia|].
  apply uint63_not_zero_spec in Hi.
  pose proof (Uint63.to_Z_bounded i).
  rewrite uint63_zero_iff in Hi. lia.
Qed.

Lemma int_to_nat_pred (i: int) (Hi: Uint63.is_zero i = false):
  int_to_nat (Uint63.pred i) = int_to_nat i - 1.
Proof.
  unfold int_to_nat. rewrite pred_to_z; auto. lia.
Qed.

(*Lemma for wf induction*)
Lemma int_pred_lt {n: int} (Hnz: Uint63.is_zero n = false):
  int_to_nat (Uint63.pred n) < int_to_nat n.
Proof.
  rewrite int_to_nat_pred; auto. apply Nat.sub_lt; try lia. unfold int_to_nat.
  rewrite uint63_not_zero_spec, uint63_zero_iff in Hnz.
  pose proof (Uint63.to_Z_bounded n). lia.
Qed.

Lemma pred_ltb {n: int} (Hnz: Uint63.is_zero n = false):
  ltb (Uint63.pred n) n = true.
Proof.
  apply Uint63.ltb_spec. rewrite pred_to_z; auto. lia.
Qed.

Lemma ltb_trans {n1 n2 n3: int} (Hlt: ltb n1 n2 = true) (Hlt2: ltb n2 n3 = true): ltb n1 n3 = true.
Proof.
  rewrite !Uint63.ltb_spec in Hlt, Hlt2 |- *. lia.
Qed.


Lemma not_ltb_zero {i n} (Hz: Uint63.is_zero n = true) (Hlt: ltb i n = true) : False.
Proof.
  rewrite Uint63.is_zero_spec in Hz. subst.
  destruct (Uint63.ltbP i 0) as [Hlt' | Hlt']; auto; try discriminate.
  pose proof (Uint63.to_Z_bounded i). rewrite Uint63.to_Z_0 in Hlt'. lia.
Qed.

Lemma ltb_leb_pred {n: int} (i: int) (Hnz: Uint63.is_zero n = false):
   ltb i n = true <-> leb i (Uint63.pred n) = true.
Proof.
  rewrite Uint63.leb_spec, Uint63.ltb_spec, pred_to_z; auto. lia.
Qed.

Lemma leb_zero {i}: leb i 0 = true -> i = 0%uint63.
Proof.
  rewrite Uint63.leb_spec. intros Hi.
  pose proof (Uint63.to_Z_bounded i). rewrite Uint63.to_Z_0 in Hi.
  apply uint63_zero_iff. lia.
Qed.

Lemma leb_pred {i n} (Hz: Uint63.is_zero n = false):
  leb i n = true <-> n = i \/ leb i (Uint63.pred n) = true.
Proof.
  rewrite !Uint63.leb_spec, pred_to_z; auto.
  assert (Heq: (n = i) <-> (Uint63.to_Z n = Uint63.to_Z i)); [| rewrite Heq; lia].
  split; [intros; subst; auto| apply Uint63.to_Z_inj].
Qed.

Lemma is_zero_ltb {n: int} (Hz: Uint63.is_zero n = false) : ltb 0 n = true.
Proof.
  rewrite Uint63.ltb_spec. apply uint63_not_zero_spec in Hz.
  rewrite Uint63.to_Z_0. pose proof (Uint63.to_Z_bounded n).
  assert (Hor: (0 < Uint63.to_Z n)%Z \/ 0%Z = Uint63.to_Z n) by lia.
  destruct Hor as [| Hzero]; auto.
  symmetry in Hzero.
  apply uint63_zero_iff in Hzero. subst. contradiction.
Qed.

End PrimInt.

(*Recursive Functions over primitive ints (from n-1 to 0)*)
(*Dependent version (uses lt info) - tricky when n = 0*)
Section IntRec.

Context (P: int -> Type) (n: int) (zero_case: forall (i: int), Uint63.is_zero i = true -> P i) 
  (pos_case: forall (i: int), Uint63.is_zero i = false -> ltb i n = true -> P (Uint63.pred i) -> P i).

(*Use Equations to get induction principle*)
Equations int_rect_aux (z: int) (z_lt: ltb z n = true) : P z by wf (int_to_nat z) lt :=
  int_rect_aux z z_lt with inspect (Uint63.is_zero z) => {
    | true eqn:Heq => zero_case z Heq
    | false eqn:Hneq => pos_case z Hneq z_lt 
      (int_rect_aux (Uint63.pred z) (ltb_trans (pred_ltb Hneq) z_lt))
  }
  .
Next Obligation.
apply int_pred_lt; assumption.
Defined.


(* Fixpoint int_rect_aux (z: int) (z_lt: ltb z n = true) (ACC: Acc lt (int_to_nat z)) : P z :=
  match Uint63.is_zero z as b return Uint63.is_zero z = b -> ltb z n = true -> P z with
  | true => fun Heq _ => eq_rect _ P zero_case _ (eq_sym (proj1 (Uint63.is_zero_spec z) Heq))
  | false => fun Hneq Hlt => pos_case z Hneq Hlt 
      (int_rect_aux (Uint63.pred z) (ltb_trans (pred_ltb Hneq) Hlt) (Acc_inv ACC (int_pred_lt Hneq)))
  end eq_refl z_lt. *)

(*First version: assume n <> 0*)
Definition int_range (Hz: Uint63.is_zero n = false) : P (Uint63.pred n) :=
  int_rect_aux (Uint63.pred n) (pred_ltb Hz) (* (Wf_nat.lt_wf _) *).

(*Gives P 0 or P 0, ..., p n-1 if n > 0*)
Definition int_range_with_zero (default: P 0) : P (if Uint63.is_zero n then 0 else (Uint63.pred n)) :=
  match Uint63.is_zero n as b return Uint63.is_zero n = b -> P (if b then 0 else (Uint63.pred n)) with
  | true => fun Hz => default
  | false => int_range
  end eq_refl.

End IntRec.

(*Use this to define iota*)
Section Iota.

Definition int_iota n := int_range_with_zero (fun _ => list int) n (fun _ _ => 0%uint63 :: nil) (fun i _ _ rec => i :: rec) nil.

Eval vm_compute in (int_iota (Uint63.of_Z 5%Z)).
(*NOTE: not computable, might need to change to eqb and use Philip's trick*)

Lemma int_iota_spec n i:
  ltb i n = true <-> List.In i (int_iota n).
Proof.
  unfold int_iota, int_range_with_zero, int_range.
  generalize dependent (@pred_ltb n).
  destruct (Uint63.is_zero n) eqn : Hnz.
  - simpl. apply Uint63.is_zero_spec in Hnz. subst. intros _.
    split; try contradiction. intros Hlt. apply not_ltb_zero in Hlt; auto.
  - intros e. generalize dependent (e eq_refl). clear e.
    setoid_rewrite (ltb_leb_pred i Hnz).
    (*use Equations ind principle*)
    generalize dependent (Uint63.pred n). 
    apply (int_rect_aux_elim _ _ _ _ (fun z Hlt l => leb i z = true <-> In i l)).
    + intros z Heq Hlt Hinspect. unfold eq_rect. 
      generalize dependent (eq_sym (proj1 (Uint63.is_zero_spec z) Heq)). intros e. subst.
      simpl. split.
      * intros Hi. apply leb_zero in Hi. subst; auto.
      * intros [Hi | []]; subst. auto.
    + intros z Hneq z_lt IH Hinspect. simpl.
      rewrite <- IH. apply leb_pred; auto.
Qed.

End Iota.

(*Array iteration*)
Section Iter.

(*dependent iteration over arrays, from n-1 to 0*)
Definition array_iter {A: Type} (a: array A) {n: int} (Hn: length a = n)
  (f: forall (i: int) (Hlt: ltb i n = true) (x: A), A) : array A :=
  match Uint63.is_zero n as b return Uint63.is_zero n = b -> array A with
  | true => fun _ => a
  | false => fun Hz => int_range (fun _ => array A) n (fun _ _ => a.[0 <- f 0%uint63 (is_zero_ltb Hz) a.[0]])
    (fun i Hnz Hlt a1 => a1.[i <- f i Hlt a.[i]]) Hz
  end eq_refl.


(*Proofs about [array_iter]*)

Lemma array_iter_length' {A: Type} (a: array A) {n: int} (Hn: length a = n)
  (f: forall (i: int) (Hlt: ltb i n = true) (x: A), A) 
  (Hnz : Uint63.is_zero n = false)
  (Hlt0 : ltb 0 n = true)
   z:
  forall e : ltb z n = true,
  length
    (int_rect_aux (fun _ : int => array A) n (fun _ _ => a.[0<-f 0%uint63 Hlt0 a.[0]])
       (fun (i : int) (_ : Uint63.is_zero i = false) (Hlt : ltb i n = true) (a1 : array A) =>
        a1.[i<-f i Hlt a.[i]]) z e) = length a.
Proof.
  apply (int_rect_aux_elim _ _ _ _ (fun _ _ l => length l = length a)).
  - intros z1 Heq Hzlt Hinspect. rewrite length_set. reflexivity.
  - intros z1 Hneq z_lt IH Hinspect.
    rewrite length_set, IH. reflexivity.
Qed.

(*iteration preserves length*)
Lemma array_iter_length {A: Type} (a: array A) {n: int} (Hn: length a = n)
  (f: forall (i: int) (Hlt: ltb i n = true) (x: A), A):
  length (array_iter a Hn f) = length a.
Proof.
  unfold array_iter, int_range. generalize dependent (@is_zero_ltb n).
  generalize dependent (@pred_ltb n). destruct (Uint63.is_zero n) eqn : Hnz; auto.
  intros e1 e2. generalize dependent (e1 eq_refl). generalize dependent (e2 eq_refl).
  clear e1 e2. intros Hlt0. apply (array_iter_length' a Hn f Hnz Hlt0).
Qed.

(*iteration sets each index to the specified value*)
Lemma array_iter_get {A: Type} (a: array A) {n: int} (Hn: length a = n)
  (f: forall (i: int) (Hlt: ltb i n = true) (x: A), A) (i: int) (Hi: ltb i n = true):
  (array_iter a Hn f).[i] = f i Hi a.[i].
Proof.
  unfold array_iter, int_range. generalize dependent (@is_zero_ltb n).
  generalize dependent (@pred_ltb n). destruct (Uint63.is_zero n) eqn : Hnz.
  - exfalso. eapply not_ltb_zero; eauto.
  - intros e1 e2. generalize dependent (e1 eq_refl). generalize dependent (e2 eq_refl).
    clear e1 e2. intros Hlt0. assert (Hi': leb i (Uint63.pred n) = true). { apply ltb_leb_pred; auto. }
    intros e.
    generalize dependent i. revert e. 
    apply (int_rect_aux_elim _ _ _ _ (fun z Hlt l => forall (i: int) (Hi: ltb i n = true), leb i z = true -> 
      l.[i] = f i Hi a.[i])).
    + intros z Hz Hzlt Hinspect i Hi Hiz. clear Hinspect. rewrite Uint63.is_zero_spec in Hz. subst.
      apply leb_zero in Hiz. subst.
      rewrite get_set_same; auto. f_equal. apply bool_irrelevance.
    + intros z Hneq z_lt IH Hinspect i Hi Hiz.
      destruct (Uint63.eqs i z).
      * subst. rewrite get_set_same; auto.
        -- f_equal. apply bool_irrelevance.
        -- rewrite array_iter_length'; auto.
      * rewrite get_set_other by auto. apply IH; auto.
        apply leb_pred in Hiz; auto. destruct Hiz; subst; auto.
Qed. 

(*Iteration preserves default*)
Lemma array_iter_default {A: Type} (a: array A) {n: int} (Hn: length a = n)
  (f: forall (i: int) (Hlt: ltb i n = true) (x: A), A):
  default (array_iter a Hn f) = default a.
Proof.
  unfold array_iter, int_range. generalize dependent (@is_zero_ltb n).
  generalize dependent (@pred_ltb n). destruct (Uint63.is_zero n) eqn : Hnz; auto.
  intros e1 e2. generalize dependent (e1 eq_refl). generalize dependent (e2 eq_refl).
  clear e1 e2. intros Hlt0.
  apply (int_rect_aux_elim _ _ _ _ (fun _ _ l => default l = default a)).
  - intros z1 Heq Hzlt Hinspect. rewrite default_set. reflexivity.
  - intros z1 Hneq z_lt IH Hinspect.
    rewrite default_set, IH. reflexivity.
Qed.

End Iter.

(*Array API:

Parameter arr : int -> (int -> Type) -> Type.
Parameter get: forall (n: int) (P: int -> Type) (i: int) (a: arr n P), option (P i).
Parameter get_dep: forall (n: int) (P: int -> Type) (a: arr n P) (i: int) (Hi: ltb i n = true), P i.
Parameter set: forall (n: int) (P: int -> Type) (i: int) (x: P i) (a: arr n P), arr n P.
Parameter make: forall (n: int) (Hn: leb n max_length = true) 
  (P: int -> Type) (init: forall (i: int) (Hi: ltb i n = true), P i),
  arr n P.
Parameter copy: forall (n: int) (P: int -> Type) (a: arr n P), arr n P.

Parameter get_none: forall (n: int) (P: int -> Type) (a: arr n P) (i: int):
  get n P i a = None <-> ltb i n = false.
Parameter get_dep_eq: forall (n: int) (P: int -> Type) (a: arr n P) (i: int) (Hi: ltb i n = true),
  get n P i a = Some (get_dep n P a i Hi).
Parameter get_set_same: forall (n: int) (P: int -> Type) (a: arr n P) (i: int) (Hi: ltb i n = true) (x: P i),
  get n P i (set n P i x a) = Some x.
Parameter get_set_other: forall (n: int) (P: int -> Type) (a: arr n P) (i j: int) (Hj: ltb j n = true) (x: P i),
  i <> j -> get n P j (set n P i x a) = get n P j a.
Parameter get_make: forall (n: int) (Hn: leb n max_length = true) (P: int -> Type) 
  (init: forall (i: int) (Hi: ltb i n = true), P i)
  (i: int) (Hi: ltb i n = true), get n P i (make n Hn P init) = Some (init i Hi).
Parameter leb_length: forall (n: int) (P: int -> Type) (a: arr n P), leb n max_length = true.
Parameter get_copy: forall (n: int) (P: int -> Type) (a: arr n P) (i: int) (Hi: ltb i n = true),
  get n P i (copy n P a) = get n P i a.
Parameter array_ext: forall (n1 n2: int) (P: int -> Type) (a1: arr n1 P) (a2: arr n2 P)
  (Hneq: n2 = n1)
  (Haeq: forall i (Hi: ltb i n1 = true), get n1 P i a1 = get n2 P i a2),
  a1 = cast (f_equal (fun n => arr n P) Hneq) a2.

(*TODO: should add something about get Some iff in bounds*)
*)

(*Array implementation*)

(*A sigma type of an index and the type. We do it separately so we can
  assume nested inductive*)
Record Box (P: int -> Type) := mk_box {
  box_i : int;
  box_data : P box_i
}.

(*The array invariants - bools for proof irrelevance*)

Definition arr_elts_def (n: int) (P: int -> Type) (a: array (option (Box P))) : bool :=
  List.forallb (fun i => 
    match a.[i] with
      | Some k => eqb (box_i P k) i
      | _ => false
      end) (int_iota n).

Lemma arr_elts_invariant (n: int) (P: int -> Type) (a: array (option (Box P))):
  arr_elts_def n P a = true <->
  forall (i: int) (Hi: ltb i n = true),
      match a.[i] with
      | Some k => box_i P k = i
      | _ => False
      end.
Proof.
  unfold arr_elts_def. rewrite List.forallb_forall. setoid_rewrite <- int_iota_spec.
  split; intros Hinvar i Hi; specialize (Hinvar i Hi); destruct (a.[i]); auto; try discriminate;
  apply Uint63.eqb_spec; auto.
Qed.

Definition isNone {A: Type} (o: option A) : bool :=
  match o with
  | None => true
  | _ => false
  end.

Lemma isNone_iff {A: Type} (o: option A):
  isNone o = true <-> o = None.
Proof.
  destruct o; split; auto; discriminate.
Qed.

(*The array*)
(*cannot bypass with record*)
#[bypass_check(nested_positivity)]
Inductive arr (n: int) (P: int -> Type) : Type :=
  | mk_arr: forall (a: array (option (Box P))), isNone (default a) = true ->
    arr_elts_def n P a = true -> eqb (length a) n = true ->
    leb n max_length = true -> arr n P.

Arguments mk_arr {_} {_}.

Definition arr_array {n P} (a: arr n P) : array (option (Box P)) :=
  match a with
  | mk_arr a _ _ _ _ => a
  end.

Definition arr_default {n P} (a: arr n P) : isNone (default (arr_array a)) = true :=
  match a with
  | mk_arr _ d _ _ _ => d
  end.

Definition arr_elts {n P} (a: arr n P) : arr_elts_def n P (arr_array a) = true :=
  match a with
  | mk_arr _ _ e _ _ => e
  end.

Definition arr_length {n P} (a: arr n P) : eqb (length (arr_array a)) n = true :=
  match a with
  | mk_arr _ _ _ l _ => l
  end.

Definition arr_max {n P} (a: arr n P) : leb n max_length = true :=
  match a with
  | mk_arr _ _ _ _ m => m
  end.
(* 

Record arr (n: int) (P: int -> Type) : Type :=
  mk_arr {
    arr_array: array (option (Box P));
    arr_default: isNone (default arr_array) = true;
    arr_elts: arr_elts_def n P arr_array = true; 
    arr_length: eqb (length arr_array) n = true;
    arr_max: leb n max_length = true }.

Arguments arr_array {_} {_}.
Arguments arr_default {_} {_}.
Arguments arr_elts {_} {_}.
Arguments arr_length {_} {_}.
Arguments arr_max {_} {_}. *)

Lemma arr_length_eq {n P} (a: arr n P):
  length (arr_array a) = n.
Proof.
  apply Uint63.eqb_correct, arr_length.
Qed.

(*Bool preds give proof irrelevance*)
Lemma arr_eq (n: int) (P: int -> Type) (a1 a2: arr n P):
  arr_array a1 = arr_array a2 ->
  a1 = a2.
Proof.
  destruct a1 as [a1 d1 e1 l1 m1]. destruct a2 as [a2 d2 e2 l2 m2]. simpl. intros Ha; subst.
  assert (Hd: d1 = d2) by (apply bool_irrelevance).
  assert (He: e1 = e2) by (apply bool_irrelevance).
  assert (Hl: l1 = l2) by (apply bool_irrelevance).
  assert (Hm: m1 = m2) by (apply bool_irrelevance).
  subst. reflexivity.
Qed.

(*Need opaque*)
Local Lemma arr_elts_impl (n: int) (P: int -> Type) i (a: array (option (Box P))) (ae: arr_elts_def n P a = true) (Hi: ltb i n = true) :
  match a.[i] with
    | Some k => box_i P k = i
    | None => False
    end.
Proof.
  exact ((proj1 (arr_elts_invariant n P a)) ae _ Hi).
Qed.

(*"get" is a bit tricky because we need a rewrite*)
Definition get(n: int) (P: int -> Type) (i: int) (a: arr n P): option (P i).
Proof.
  destruct (ltb i n) eqn : Hi; [| exact None].
  pose proof (arr_elts_impl n P i (arr_array a) (arr_elts a) Hi) as Heq.
  destruct (arr_array a).[i] as [k|]; [|contradiction].
  destruct k as [ki kd]. simpl in Heq. rewrite <- Heq. exact (Some kd).
Defined.

(*We prove the obligations separately for "set" so they are opaque*)

Lemma set_default_obligation (n: int) (P: int -> Type) (a: arr n P) (i: int) (Hi: ltb i n = true) (x: P i):
  isNone (default (arr_array a).[i<-Some {| box_i := i; box_data := x |}]) = true.
Proof.
  rewrite default_set. apply arr_default.
Qed.

Lemma set_elts_obligation (n: int) (P: int -> Type) (a: arr n P) (i: int) (Hi: ltb i n = true) (x: P i):
  arr_elts_def n P (arr_array a).[i<-Some {| box_i := i; box_data := x |}] = true.
Proof.
  apply arr_elts_invariant.
  intros j Hj. destruct (eqb i j) eqn : Heq.
  + apply Uint63.eqb_correct in Heq. subst. rewrite get_set_same; simpl; auto.
    rewrite arr_length_eq. auto.
  + apply Uint63.eqb_false_correct in Heq. rewrite get_set_other; auto.
    apply (proj1 (arr_elts_invariant n P (arr_array a))); auto.
    apply arr_elts.
Qed.

Lemma set_length_obligation (n: int) (P: int -> Type) (a: arr n P) (i: int) (Hi: ltb i n = true) (x: P i):
  eqb (length (arr_array a).[i<-Some {| box_i := i; box_data := x |}]) n = true.
Proof.
  rewrite length_set. apply arr_length.
Qed.

Lemma leb_length (n: int) (P: int -> Type) (a: arr n P):
  leb n max_length = true.
Proof.
  destruct a; auto.
Qed.

Definition set_arr (n: int) (P: int -> Type) (a: arr n P) (i: int) (Hi: ltb i n = true) (x: P i) : arr n P.
Proof.
set (newarr := (arr_array a).[i <- Some (mk_box P i x)]).
apply (mk_arr newarr).
- apply set_default_obligation; assumption.
- apply set_elts_obligation; assumption.
- apply set_length_obligation; assumption.
- apply (arr_max a). 
Defined.

Definition set (n: int) (P: int -> Type) (i: int) (x: P i) (a: arr n P): arr n P.
Proof.
  destruct (ltb i n) eqn : Hlt; [| exact a].
  apply (set_arr n P a i Hlt x).
Defined.

(*"get" and "set" specs - lots of tricky dependent types*)
Lemma get_set_same: forall (n: int) (P: int -> Type) (a: arr n P) (i: int) (Hi: ltb i n = true) (x: P i),
  get n P i (set n P i x a) = Some x.
Proof.
  intros n P a i Hi x.
  unfold get, set. simpl. generalize dependent (@eq_refl _ (ltb i n)).
  unfold set_arr.
  generalize dependent (set_default_obligation n P a i).
  generalize dependent (set_elts_obligation n P a i).
  generalize dependent (set_length_obligation n P a i). simpl.
  generalize dependent (arr_elts_impl n P i) . simpl.
  rewrite Hi. simpl.
  intros Helts1 _ Helts2 _ Heq. 
  generalize dependent (Helts1 (arr_array a).[i<-Some {| box_i := i; box_data := x |}] (Helts2 Heq x) Heq).
  destruct (arr_array a).[i<-Some {| box_i := i; box_data := x |}].[i] as [k|] eqn : Ha;
  simpl; [| contradiction].
  (*The reasonable goal*)
  intros Hieq. subst. destruct k; simpl in *.
  rewrite get_set_same in Ha. inversion Ha as [ Hx]; subst.
  apply Eqdep_dec.inj_pair2_eq_dec in Hx; subst; auto.
  - apply Uint63.eqs.
  - rewrite arr_length_eq. auto.
Qed.

Lemma get_set_other: forall (n: int) (P: int -> Type) (a: arr n P) (i j: int) (Hj: ltb j n = true) (x: P i),
  i <> j -> get n P j (set n P i x a) = get n P j a.
Proof.
  intros n P a i j Hj x Hij.
  unfold get, set. simpl.
  generalize dependent (arr_elts_impl n P j).
  rewrite Hj.
  unfold set_arr.
  generalize dependent (set_default_obligation n P a i).
  generalize dependent (set_elts_obligation n P a i).
  generalize dependent (set_length_obligation n P a i). simpl.
  destruct (ltb i n) eqn : Hi; simpl.
  - (*in bounds*) intros _ Helts1 _ Helts2.
    generalize dependent (Helts2 (arr_array a).[i<-Some {| box_i := i; box_data := x |}] (Helts1 eq_refl x) eq_refl).
    destruct (arr_array a).[i<-Some {| box_i := i; box_data := x |}].[j] eqn : Ha; simpl; [| contradiction].
    intros Hjeq. subst. destruct b as [bi bd]. simpl in *.
    generalize dependent (Helts2 (arr_array a) (arr_elts a) eq_refl). clear Helts2 Helts1.
    destruct (arr_array a).[bi] eqn : Ha1; [| contradiction]. intros Hbi; subst.
    destruct b as [bi' bd']; simpl in *.
    rewrite get_set_other in Ha; auto. rewrite Ha1 in Ha. inversion Ha as [Hx].
    apply Eqdep_dec.inj_pair2_eq_dec in Hx; subst; auto. apply Uint63.eqs.
  - (*out of bounds*) intros; reflexivity.
Qed.

Lemma get_none (n: int) (P: int -> Type) (a: arr n P) (i: int):
  get n P i a = None <-> ltb i n = false.
Proof.
  unfold get. generalize dependent (arr_elts_impl n P i (arr_array a) (arr_elts a)). 
  destruct (ltb i n) eqn : Hi; simpl; [| split; auto]. intros Helts.
  split; [|discriminate].
  generalize dependent (Helts eq_refl). clear Helts.
  destruct (arr_array a).[i] eqn : Ha; [| contradiction].
  intros Hieq; subst. destruct b; simpl in *. discriminate.
Qed.

(*As a corollary, a dependently typed version of "get"*)
Definition get_dep (n: int) (P: int -> Type) (a: arr n P) (i: int) (Hi: ltb i n = true) : P i :=
  match (get n P i a) as o return get n P i a = o -> P i with
  | Some k => fun _ => k
  | None => fun Hget => False_rect _ (Bool.eq_true_false_abs _ Hi (proj1 (get_none n P a i) Hget))
  end eq_refl.

Lemma get_dep_eq (n: int) (P: int -> Type) (a: arr n P) (i: int) (Hi: ltb i n = true):
  get n P i a = Some (get_dep n P a i Hi).
Proof.
  unfold get_dep. generalize dependent ((proj1 (get_none n P a i))). 
  destruct (get n P i a); simpl; auto. intros e. exfalso.
  rewrite e in Hi; auto. discriminate.
Qed.

(*Extensionality*)
Lemma array_ext: forall (n1 n2: int) (P: int -> Type) (a1: arr n1 P) (a2: arr n2 P)
  (Hneq: n2 = n1)
  (Haeq: forall i (Hi: ltb i n1 = true), get n1 P i a1 = get n2 P i a2),
  a1 = cast (f_equal (fun n => arr n P) Hneq) a2.
Proof.
  intros n1 n2 P a1 a2 Hneq Hget. subst. simpl.
  apply arr_eq, array_ext.
  - rewrite !arr_length_eq. reflexivity.
  - rewrite arr_length_eq. intros i Hlt. specialize (Hget i Hlt).
    revert Hget. unfold get.
    generalize dependent (arr_elts_impl n1 P i). rewrite Hlt.
    intros Helts. generalize dependent (Helts (arr_array a1) (arr_elts a1) eq_refl).
    generalize dependent (Helts (arr_array a2) (arr_elts a2) eq_refl). clear Helts.
    destruct (arr_array a1).[i] eqn : Ha1; [| contradiction].
    destruct (arr_array a2).[i] eqn : Ha2; [| contradiction].
    intros Hi1 Hi2. subst. destruct b as [bi1 bd1]. destruct b0 as [bi2 bd2]. simpl in *.
    subst. simpl. intros Hbd. inversion Hbd; subst. reflexivity.
  - assert (Hd1: default (arr_array a1) = None). { apply isNone_iff, arr_default. }
    rewrite Hd1. symmetry. apply isNone_iff, arr_default.
Qed.

(*Define "make" in pieces like "set"*)
Lemma length_make' {n: int} {A: Type} {x: A} (Hn: leb n max_length = true) : length (make n x) = n.
Proof.
  rewrite length_make, Hn. reflexivity.
Qed.

Definition make_arr (n: int) (Hn: leb n max_length = true) (P: int -> Type) (init: forall (i: int) (Hi: ltb i n = true), P i):
  array (option (Box P)) :=
  array_iter (make n None) (length_make' Hn) (fun i (Hi: ltb i n = true) _ => Some (mk_box _ i (init i Hi))).

Lemma make_default_obligation (n: int) (Hn: leb n max_length = true) (P: int -> Type) 
  (init: forall (i: int) (Hi: ltb i n = true), P i):
  isNone (default (make_arr n Hn P init)) = true.
Proof.
  unfold make_arr. rewrite array_iter_default, default_make. reflexivity.
Qed.

Lemma make_elts_obligation (n: int) (Hn: leb n max_length = true) (P: int -> Type) 
  (init: forall (i: int) (Hi: ltb i n = true), P i):
  arr_elts_def n P (make_arr n Hn P init) = true.
Proof.
  apply arr_elts_invariant. intros i Hi.
  unfold make_arr. rewrite array_iter_get with (Hi:=Hi). reflexivity.
Qed.

Lemma make_length_obligation (n: int) (Hn: leb n max_length = true) (P: int -> Type) 
  (init: forall (i: int) (Hi: ltb i n = true), P i):
  eqb (length (make_arr n Hn P init)) n = true.
Proof.
  unfold make_arr. rewrite array_iter_length, length_make, Hn, Uint63.eqb_refl. reflexivity.
Qed.

Definition make (n: int) (Hn: leb n max_length = true) 
  (P: int -> Type) (init: forall (i: int) (Hi: ltb i n = true), P i):
  arr n P :=
  mk_arr (make_arr n Hn P init)
  (make_default_obligation n Hn P init)
  (make_elts_obligation n Hn P init)
  (make_length_obligation n Hn P init) Hn.

(*The property of "make" (length is implicity like "set")*)
Lemma get_make (n: int) (Hn: leb n max_length = true) (P: int -> Type) 
  (init: forall (i: int) (Hi: ltb i n = true), P i)
  (i: int) (Hi: ltb i n = true): 
  get n P i (make n Hn P init) = Some (init i Hi).
Proof.
  unfold get, make. simpl.
  generalize dependent (arr_elts_impl n P i (make_arr n Hn P init)).
  assert (Hmake: (make_arr n Hn P init).[i] = Some (mk_box _ i (init i Hi))).
  {
    unfold make_arr. rewrite array_iter_get with (Hi:=Hi). reflexivity. 
  }
  rewrite Hmake. simpl. intros Heq.
  clear Hmake.
  (*Now we can generalize init*)
  generalize dependent (init i).
  generalize dependent (Heq (make_elts_obligation n Hn P init)).
  rewrite Hi; simpl. intros e1 e2.
  generalize dependent (e1 eq_refl). intros e. 
  assert (e = eq_refl). {
    apply UIP_dec, Uint63.eqs. 
  }
  subst. reflexivity.
Qed.

(*"copy" is similar to "make" but simpler*)
Definition copy_arr (n: int) (P: int -> Type) (a: arr n P) : array (option (Box P)) :=
  copy (arr_array a).

Lemma copy_default_obligation (n: int) (P: int -> Type) (a: arr n P):
  isNone (default (copy_arr n P a)) = true.
Proof.
  unfold copy_arr. rewrite default_copy. apply arr_default.
Qed.

Lemma copy_elts_obligation (n: int) (P: int -> Type) (a: arr n P):
  arr_elts_def n P (copy_arr n P a) = true.
Proof.
  apply arr_elts_invariant. intros i Hi.
  unfold copy_arr. rewrite get_copy. eapply arr_elts_impl; eauto. apply arr_elts.
Qed.

Lemma copy_length_obligation (n: int) (P: int -> Type) (a: arr n P):
  eqb (length (copy_arr n P a)) n = true.
Proof.
  unfold copy_arr. rewrite length_copy. apply arr_length.
Qed.

Definition copy (n: int) (P: int -> Type) (a: arr n P): arr n P :=
  mk_arr (copy_arr n P a) (copy_default_obligation n P a) (copy_elts_obligation n P a)
    (copy_length_obligation n P a) (leb_length n P a).

Lemma get_copy (n: int) (P: int -> Type) (a: arr n P) (i: int) (Hi: ltb i n = true):
  get n P i (copy n P a) = get n P i a.
Proof.
  unfold get, copy. simpl.
  generalize dependent (arr_elts_impl n P i (copy_arr n P a) (copy_elts_obligation n P a)).
  generalize dependent (arr_elts_impl n P i (arr_array a) (arr_elts a)).
  rewrite Hi.
  intros Helts1 Helts2.
  generalize dependent (Helts1 eq_refl).
  generalize dependent (Helts2 eq_refl). clear Helts1 Helts2.
  assert (Hcopy: (copy_arr n P a).[i] = (arr_array a).[i]).
  { unfold copy_arr. rewrite get_copy. reflexivity. }
  rewrite Hcopy.
  destruct (arr_array a).[i] eqn : Ha; [| contradiction].
  intros Hi1 Hi2; subst. destruct b. f_equal. apply UIP_dec, Uint63.eqs.
Qed. 

