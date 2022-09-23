(** Introduction to Coq exercises for the Bindel group meeting 09/23/2022 **)

(** Note: In the web-based environment for Coq, you can move down through proof
   scripts using Alt+p and up through proof scripts using Alt+n . **)


(** Example Set 1 **)
Theorem id_test : 
forall P : Prop, P -> P.
Proof.
(* apply the inference rule of implication elimination, using the intros tactic *)
intros P.
(* The Show Proof command displays the proof object that's been built so far. Incomplete
  parts of the proof -- holes -- are denoted with a ? prefix. *)
Show Proof.
(* apply the inference rule of implication elimination, using the intros tactic *)
intros X.
Show Proof.
(* TODO *)
Admitted.

(* We can see id_test's proof object and type using the Print command. *)

Print id_test.

(* We can provide the proof object directly as an alternative proof. *)

Theorem id_test_alt: 
forall P : Prop, P -> P.
Proof.
apply (fun P => fun X => X).
Qed.

Print id_test_alt.


Theorem app_test1 :
  forall A B , (A -> B) -> A -> B.
Proof.
(* Function application binds tighter than abstraction. *)
apply (fun A B => fun HAB => fun HA => HAB HA).
Qed.

Theorem app_test2 :
  forall A B C, (A -> B) -> (B -> C) -> A -> C.
Proof.
apply (fun A B C => fun HAB HBC HA => HBC (HAB HA)).
Qed.

Theorem app_test3 :
  forall A B C, (A -> B -> C) -> A -> B -> C.
Proof.
(* Function application is left associative. *)
apply (fun A B C => fun HABC A B => HABC A B).
Qed.


(** Example Set 2 : Inductive Definitions **)
Module BindelGroupIntro.
(** NOTE : Module System **)
(** All declarations between Module X and End X markers are referred to by names like X.foo 
in the remainder of the file (instead of just foo). Use this feature to limit the scope of 
definitions, so that you can reuse names. **)

(** From Software Foundations: "The set of built-in features in Coq is extremely small. 
For example, instead of providing the usual palette of atomic data types 
(booleans, integers, strings, etc.), Coq offers a powerful mechanism for 
defining new data types from scratch, with all these familiar types as instances.
Naturally, the Coq distribution comes with an extensive standard library providing 
definitions of booleans, numbers, and many common data structures like lists and hash tables. 
But there is nothing magic or primitive about these library definitions". **)

(** We can define a new type inductively, called day, whose members are monday, tuesday, etc. **)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(** An Inductive definition does two things:
(#1.) It defines a set of new constructors. monday is a constructor.
(#2.) It groups them into a new named type. day is a new named type. **)

(** day is the type of the constructor monday **)
Check monday.
(** Set is the type of day. **)
Check day.
(** Type is the type of Set. *)
Check Set.

(** Having defined day, we can write functions that operate on days. **)

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | _ => monday
  end.

End BindelGroupIntro.


(** Every nat is either built with O or with S. **)
Print nat.
(** What's the type of S ? **)
Check S.
(* If a nat is built with S we can extract the underlying natural number. *)
Check S O.

Definition minus_one (n : nat) : nat :=
  match n with 
    | 0 => 0
    | S n' => n'
  end.

Check minus_one.

(** Observe that minus_one and S appear to have the same type. 
 In fact S is more than just a function nat -> nat: we can pattern 
 match on S but we can't pattern match on minus_one. **)

(*
Definition minus_two (n: nat) : nat :=
  match n with 
    | O => O
    | minus_one n' => minus_one n'
  end.
*)


(** TODO : define minus_two **)

(** Coq provides several evaluation mechanisms. **)
Eval compute in (minus_one (S ( S 0))).

(** There are different ways to define objects in 
 Coq. We can construct a definition of
 "minus_one" in "proof mode." **)
Definition minus_one_transparent (n : nat) : nat.
exact (n - 1). Defined.

Print minus_one.
Print minus_one_transparent.

(** Defined marks a definition as transparent, 
allowing it to be unfolded; Qed marks a definition as 
opaque, preventing unfolding. *)
Eval compute in (minus_one_transparent 3).

Definition minus_one_opaque (n : nat) : nat.
exact (n - 1). Qed.

Eval compute in (minus_one_opaque 3).

Lemma equal_defs n :
minus_one n = minus_one_transparent n.
Proof.
unfold minus_one_transparent, minus_one.
(* Perform case analysis by generating a subgoal 
 for each constructor of the inductive type using the
 destruct tactic *)
destruct n.
- (* bullets allow us to focus on a subgoal *)
(* how do we finish this proof? *)
(* we can look at available lemmas *)
Search (0 - _)%nat.
Abort.

(** a standard prelude module provides the standard logic connectives, 
and a few arithmetic notions. If you want to load and open other modules 
from the library, you have to use the Require command. **)

Require Import Arith.

(* we can look at available lemmas *)
Search ( 0 - _)%nat.

Lemma equal_defs n :
minus_one n = minus_one_transparent n.
Proof.
unfold minus_one_transparent, minus_one.
destruct n.
-
rewrite Nat.sub_0_l.
reflexivity.
-
rewrite Nat.sub_1_r.
rewrite Nat.pred_succ.
reflexivity.
Qed.

(** Example Set 3: Recursive Functions & Inductively Defined Properties **)

(** Recursive functions are defined with the keyword Fixpoint instead of Definition.**) 
Print fact.

Eval compute in (fact 4).

(** We can express the concept "m is n!" as an inductively defined property of 
  natural numbers. **) 

Inductive fact_rel : nat -> nat -> Prop :=
  | zero : fact_rel 0 1 (* "1 is 0!" *)
  | plus_one : forall n m, fact_rel n m -> fact_rel (n + 1) (( n + 1) * m)
    (* "if m is n! then (n+1) * m is (n + 1)!" *)
    .

Check zero.

(* import some tactics for integers *)
Require Import Lia.


Theorem fact_correct1 :
  forall (n m : nat), fact_rel n (fact n).
Proof.
intros; induction n. 
-
apply zero.
(* can also use the tactic "constructor" *)
-
unfold fact.
replace (S n) with (n + 1)%nat by lia.
constructor.
fold fact.
exact IHn.
Qed.


(** Example Set 4: Real Analysis **)

(** The literature: "Coquelicot: A User-Friendly Library of Real Analysis for Coq" 
  by Sylvie Boldo and co-authors. **)
Require Import Reals.
(** "The formalization of real numbers from the standard library is axiomatic 
rather than definitional. Instead of building reals as Cauchy sequences or
Dedekind cuts of rational numbers and proving their properties, Coq developers 
have assumed the existence of a set with the usual properties of the real line." **)

Require Import Coquelicot.Coquelicot.


