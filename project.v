(* -------------------------------------------------------------------- *)
Require Import Bool Arith List ssreflect.


Local Notation "~~ b" := (negb b) (at level 2).
Local Notation "b1 == b2" := (eqb b1 b2) (at level 70).

(* -------------------------------------------------------------------- *)
(* We are here interested in proving facts about propositional logic.   *
 *                                                                      *
 * The purpose of this exercice is the proof of the 2 following facts:  *
 * - 1. natural deduction is correct w.r.t. the interpretation of       *
 *      assertions;                                                     *
 * - 2. it is decidable to check that an assertion is universally       *
 *      valid. We are going to check that by implementing a sound       *
 *      normalization algorithm for assertions, and then to write, in   *
 *      Coq, a simple decision for the universal validity of the        *
 *      normalized assertions.                                          *)

(* ==================================================================== *)
(* The following datatype describe the syntax of assertions. The        *
 * constructors for True, the negation and the double implication       *
 * are not primitive. They are expressed using the other constructions  *
 * of the logic.                                                        *)
 
Inductive prop : Type :=
| PVar (_ : nat)                (* Propositional variable *)
| PFalse                        (* False *)
| PAnd (_ : prop) (_ : prop)    (* Conjunction *)
| POr  (_ : prop) (_ : prop)    (* Disjunction *)
| PImp (_ : prop) (_ : prop).   (* Implication *)

Notation PTrue    := (PImp PFalse PFalse).
Notation PNot p   := (PImp p PFalse).
Notation PIff p q := (PAnd (PImp p q) (PImp q p)).

(* -------------------------------------------------------------------- *)
(* A valuation is simply a function from propositional variables to     *
 * truth values.                                                        *)

Notation valuation := (nat -> bool) (only parsing).

(* -------------------------------------------------------------------- *)
(* Complete the definition of the following function that computes the  *
 * semantic of an assertion from the given valuation.                   *)

Print andb.

Fixpoint sem (v : valuation) (p : prop) : bool :=
  match p with
  | PVar a => v a
  | PFalse => false
  | PAnd a b =>  andb (sem v a)  (sem v b)
  | POr a b => if (sem v a) then   true else (sem v b)
  | PImp a b => 
          match (sem v a) with
               | false => true
               | true => (sem v b)
               end

  end.
(* -------------------------------------------------------------------- *)
(* We now define the notions of begin satisfiable under a valuation     *
 * and of being universally valid.                                      *)

Definition sat (v : valuation) (p : prop) :=
  sem v p = true.

Definition valid (p : prop) :=
  forall v, sat v p.

(* -------------------------------------------------------------------- *)
(* The following inductive predicate defines the notion of judgement    *
 * in natural deduction. This predicate accepts two arguments:          *
 *                                                                      *
 * - a list of assertions that stands for the proof context;            *
 * - the assertion that is proven under this context.                   *)

Inductive nd : list prop -> prop -> Prop :=
  (* Non-structural rules *)
| Ax env p :
    In p env -> nd env p

| Absurd env p :
    nd (PNot p :: env) PFalse -> nd env p

  (* Introduction rules *)

| AndI   env p q : nd env p -> nd env q -> nd env (PAnd p q)
| OrIL   env p q : nd env p -> nd env (POr p q)
| OrIR   env p q : nd env q -> nd env (POr p q)
| ImpI   env p q : nd (p :: env) q -> nd env (PImp p q)

  (* Elimination rules *)

| FalseE env p     : nd env PFalse -> nd env p
| AndEL  env p q   : nd env (PAnd p q) -> nd env p
| AndER  env p q   : nd env (PAnd p q) -> nd env q
| OrE    env p q r : nd env (POr p q) -> nd (p :: env) r -> nd (q :: env) r -> nd env r
| ImpE   env p q   : nd env p -> nd env (PImp p q) -> nd env q
.

(* -------------------------------------------------------------------- *)
(* We first start to prove that the predicate [dn] is stable by         *
 * weakening or permuting the proof context. The following definition   *
 * defines an ordering over proof contexts.                             *)

Definition subenv (e1 e2 : list prop) :=
  forall q, In q e1 -> In q e2.

(* -------------------------------------------------------------------- *)
(* Show that [dn] is monotone from [subenv]                             *)

Lemma subenv_nd (e1 e2 : list prop) (p : prop) :
  subenv e1 e2 -> nd e1 p -> nd e2 p.
Proof.
intros i12 d.
move: e2 i12.
induction d => e2 i12.
apply Ax. apply i12. assumption. 
apply Absurd. apply IHd. move => q. simpl. move => [A|B]. left. assumption. right. apply i12. assumption. apply AndI. apply IHd1. assumption. apply IHd2. assumption. 
apply OrIL. apply IHd. assumption. apply OrIR. apply IHd. assumption. apply ImpI.
apply IHd. move => k. simpl. move => [A|B]; auto. apply FalseE. apply IHd. auto.
apply AndEL with q. auto. apply AndER with p. auto. apply OrE with p q. auto.
apply IHd2. move => A. simpl. move => [B|C]; auto. apply IHd3. move => A. simpl. move => [B|C]; auto. apply ImpE with p; auto.
Qed.

(* -------------------------------------------------------------------- *)
(* We now prove the correctness of [dn]. Prove the following lemma,     *
 * by induction on [nd env p].                                          *)



Lemma correctness (env : list prop) (p : prop) :
  nd env p -> forall v, (forall q, In q env -> sat v q) -> sat v p.
Proof.

intros.
induction H; auto; unfold sat.
case vp:(sem v p); auto.
apply IHnd; intros; auto. 
case H1; intros. rewrite -H2.
unfold sat; simpl; rewrite vp; auto.
apply H0. apply H2.

simpl; rewrite IHnd1 ?IHnd2;auto.
simpl; rewrite IHnd; auto.
simpl; rewrite IHnd; auto.
case vp:(sem v p); auto.

simpl. 
case vp:(sem v p). 
apply IHnd.
intros.
case H1.
intros.
rewrite -H2.
unfold sat; apply vp.
intros;auto.
trivial.

case vp:(sem v p); auto.
apply IHnd. intros;auto.

case vp: (sem v p);auto.
unfold sat in IHnd. simpl in IHnd. 
rewrite vp in IHnd; auto.

case vq: (sem v q);auto.
unfold sat in IHnd. simpl in IHnd.
rewrite vq in IHnd. case vp: (sem v p). 
rewrite vp in IHnd;auto.
rewrite vp in IHnd;auto.

unfold sat in IHnd1, IHnd2, IHnd3.
simpl in IHnd1, IHnd2, IHnd3.
case vp:(sem v p); case vq:(sem v q); case vr:(sem v r); auto;rewrite vr in IHnd2, IHnd3.
rewrite vp in IHnd1. apply IHnd2. intros.
case H3. intros. rewrite -H4; auto.
intros; apply H0. apply H4.

apply IHnd2. intros. case H3.
intros. rewrite -H4. apply vp.
intros. apply H0; auto.

apply IHnd3. intros. case H3.
intros. rewrite -H4; auto.
intros. apply H0; auto.

rewrite vq in IHnd1; rewrite vp in IHnd1; apply IHnd1.
intros. apply H0; auto.

case vq: (sem v q); auto.
case vp: (sem v p); auto.
unfold sat in IHnd1, IHnd2.
simpl in IHnd1, IHnd2.
rewrite vp in IHnd1, IHnd2.
rewrite vq in IHnd2.
apply IHnd2; intros.
apply H0; apply H2.

unfold sat in IHnd1, IHnd2.
simpl in IHnd1, IHnd2.
rewrite vp in IHnd1, IHnd2.
apply IHnd1; intros.
apply H0.
apply H2.
Qed.


(* ==================================================================== *)
(* We are now interested in deciding if a given assertion is            *
 * universally valid or not. For that, we first normalize the           * 
 * assertions, obtaining an expression built from boolean constants,    *
 * propositionnal variables and if-then-else statements whose           *
 * condition is a propositional variables.                              *)

(* -------------------------------------------------------------------- *)
(* We start by defining an intermediate datatype that describe the      *
 * syntax of normalized assertions, except for the side conditions      *
 * of the if-then-else expressions that are still unconstrained.        *)

Inductive ifForm : Type :=
| PIVar   (_ : nat)                               (* variable propositionnelle *)
| PIConst (_ : bool)                              (* constante true / false *)
| PIIf    (_ : ifForm) (_ : ifForm) (_ : ifForm). (* if-then-else *)

(* -------------------------------------------------------------------- *)
(* Define the semantic of the assertions of type [ifForm].              *)

Fixpoint ifsem (v : valuation) (p : ifForm) : bool :=
  match p with
  | PIVar a => v a
  | PIConst a => a
  | PIIf a b c =>
      match (ifsem v a) with
          | true => (ifsem v b)
          | false => (ifsem v c)
      end 
  end.

(* -------------------------------------------------------------------- *)
(* Write the normalization functions from assertions of type [prop] to  *
 * assertions of type [ifForm].                                         *)

Fixpoint ifForm_of_prop (p : prop) :=
match p with 
  | PVar a => PIVar a 
  | PFalse => PIConst false
  | PAnd a b => PIIf (ifForm_of_prop a)(ifForm_of_prop b) (PIConst false)
  | POr a b => PIIf (ifForm_of_prop a) (PIConst true) (ifForm_of_prop b)
  | PImp a b => PIIf (ifForm_of_prop a) (ifForm_of_prop b) (PIConst true)
  end.

(* -------------------------------------------------------------------- *)
(* Show that your normalization function is correct w.r.t. [ifsem].     *)

Lemma ifForm_correct (v : valuation) (p : prop) :
  sem v p = ifsem v (ifForm_of_prop p).
Proof.
induction p; auto.  simpl. rewrite IHp1. rewrite IHp2. auto. 
simpl. rewrite IHp1. rewrite IHp2. auto. simpl. rewrite IHp1. rewrite IHp2. auto.
Qed.

(* -------------------------------------------------------------------- *)
(* We now define the syntax of normalized assertions. We see that the   *
 * conditions of the if-then-else expressions are now enforced to be    *
 * propositional variables.                                             *)

Inductive nifForm : Type :=
| PNIVar   (_ : nat)
| PNIConst (_ : bool)
| PNIIf    (_ : nat) (_ : nifForm) (_ : nifForm).

(* -------------------------------------------------------------------- *)
(* Define the semantic of the assertions of type [nifForm].             *)

Fixpoint nifsem (v : valuation) (p : nifForm) : bool :=
  match p with
  | PNIVar a => v a
  | PNIConst a => a
  | PNIIf a B C => 
      match (v a) with
          | true => (nifsem v B)
          | false => (nifsem v C)
      end
  end. 

(* -------------------------------------------------------------------- *)
(* Write below the normalization function for assertions of type        *
 * [ifForm], obtaining assertions of type [nifForm].                    *)

Fixpoint normif (c t f : nifForm) {struct c} : nifForm :=
   match c with
   | PNIVar a => PNIIf a t f
   | PNIConst a => 
      match a with
        | true => t
        | false => f
        end
   | PNIIf n p q => PNIIf (n) (normif p t f) (normif q t f)
   end. 

Fixpoint norm (p : ifForm) : nifForm :=
   match p with
   | PIVar a => PNIVar a
   | PIConst b => PNIConst b
   | PIIf a b c => normif (norm a) (norm b) (norm c)
   end.

(* -------------------------------------------------------------------- *)
(* Show that the normalization functions are correct w.r.t. [nifsem].   *)

Lemma normif_correct (v : valuation) (c t f : nifForm) :
  nifsem v (normif c t f) = if nifsem v c then nifsem v t else nifsem v f.
Proof. elim c; simpl; auto.
intros. case b; auto. intros. rewrite H. rewrite H0. case v; done.
Qed.

(* -------------------------------------------------------------------- *)
Lemma norm_correct (v : valuation) (p : ifForm) : nifsem v (norm p) = ifsem v p.
Proof.
induction p. auto. simpl. auto. simpl. 
rewrite normif_correct. rewrite IHp1. rewrite IHp2; rewrite IHp3. auto. Qed.



(* -------------------------------------------------------------------- *)
(* Finally, we provide a procedure that decides if a normalized         *
 * assertion is universally valid w.r.t. [nifasm].                      *)

Definition xt (v : nat -> option bool) (x : nat) (b : bool) :=
  fun y => if beq_nat x y then Some b else v y.

Fixpoint nifForm_tauto_r (v : nat -> option bool) (p : nifForm) :=
  match p with
  | PNIVar   x => match v x with Some true => true | _ => false end
  | PNIConst b => b

  | PNIIf x t f =>
    match v x with
    | Some true  => nifForm_tauto_r v t
    | Some false => nifForm_tauto_r v f
    | None       =>
           nifForm_tauto_r (xt v x true ) t
        && nifForm_tauto_r (xt v x false) f
    end
  end.

Definition nifForm_tauto p := nifForm_tauto_r (fun _ => None) p.

(* -------------------------------------------------------------------- *)
(* Show the correctness of the procedure...                             *)


Lemma nifForm_tauto_r_correct (xv : nat -> option bool) (p : nifForm) :
     nifForm_tauto_r xv p = true
  -> forall v, (forall x b, xv x = Some b -> v x = b)
       -> nifsem v p = true.
Proof.
move: xv; induction p; auto. simpl. intros. apply H0. move :H. case (xv n) => //=.
case => b; auto. move: b. discriminate.

simpl. intros.
case xvx : (xv n) => [[|]|]//=; try (move: (H0 n _ xvx) => e; rewrite e /=).
apply (IHp1 xv); auto.
by rewrite xvx in H.
apply (IHp2 xv); auto.
by rewrite xvx in H.
rewrite xvx in H.

case v0n : (v n).
apply IHp1 with (xt xv n true); auto.

move: H; case (nifForm_tauto_r _ _)=> //=.
move => x b; unfold xt.
case nx: (_ =? _); last auto.
apply beq_nat_true_iff in nx.
case b. rewrite -nx; auto.
discriminate.

move: H; case (nifForm_tauto_r _ _) => //=.
case c2: (nifForm_tauto_r _ _) => //=.
move=> t. 
apply IHp2 with (xt xv n false)=>//=.
move => x b; unfold xt.
case nx: (_ =? _); last auto.
apply beq_nat_true_iff in nx.
case b. rewrite -nx; auto.
discriminate. 
rewrite -nx; auto.
Qed.

Lemma auxiliary: 
forall p b, (nifForm_tauto (p) = b) = (nifForm_tauto_r (fun _ => None) (p) = b).
auto. Qed.



(* -------------------------------------------------------------------- *)
Lemma nifForm_tauto_correct (p : nifForm) :
  nifForm_tauto p = true -> forall v, nifsem v p = true.
Proof.
induction p => //=. rewrite auxiliary. simpl. intros. case a: (v n). move :H.
case c2: (nifForm_tauto_r _ p2). rewrite andb_comm /=. intros. 

apply (nifForm_tauto_r_correct _ _ ) with v in H. auto. unfold xt. intros.
move: H0. case nx: (n=?x). case b. apply beq_nat_true_iff in nx. rewrite -nx. auto.
discriminate. case b. discriminate. discriminate. rewrite andb_comm /=; discriminate.
move :H.
case c2: (nifForm_tauto_r _ p1) => //=. intros. apply (nifForm_tauto_r_correct _ _ ) with v in H.
auto. intros. move :H0. unfold xt. case nx: (n=?x). case b. discriminate. apply beq_nat_true_iff in nx.
rewrite -nx. auto. discriminate. Qed.



(* -------------------------------------------------------------------- *)
(* ...and its completness.                                              *)
Lemma auxiliary3:
forall b: bool, forall a:bool, forall c:bool, (Some b = Some b -> a = c) -> a = c.
auto. 
Qed.

Lemma nifForm_tauto_r_complete (xv : nat -> option bool) (p : nifForm) :
     nifForm_tauto_r xv p = false
  -> exists v, (forall x b, xv x = Some b -> v x = b) /\ nifsem v p = false.
Proof.
move : xv.  
induction p => //=.
 intros.
exists (fun x => match xv x with Some true => true | _ => false end).
split. intros. move :H0. case (xv x) => //=. move => b0. case b0. case b => //=. case b => //=.
auto. 

case b. move => a. discriminate. intros. exists (fun x => match xv x with Some true => true | _ => false end).
split. intros. move: H0. case (xv x) => //=. move => b1. case b0. case b1 => //=. case b1 => //=. auto.
intros. move: H. 
case xvn: (xv n) => [a]. case na: a. move => A. apply IHp1 in A. 
destruct A. exists x. move :H. move => [A B]. split. auto. rewrite na in xvn.
move : (A n a). rewrite xvn. rewrite na. intros. apply auxiliary3 in A0. rewrite A0.
auto.
move => A. apply IHp2 in A. 
destruct A. exists x. move :H. move => [A B]. split. auto. rewrite na in xvn.
move : (A n a). rewrite xvn. rewrite na. intros. apply auxiliary3 in A0. rewrite A0.
auto.
case XV:(nifForm_tauto_r _ _)=> //=.
move => A. move :(IHp2 (xt xv n false)). move => whol. apply whol in A. 
destruct A. exists x.
Focus 2. intros. move: (IHp1 (xt xv n true)). move => A. apply A in XV. 
destruct XV. exists x. move: H0. move => [B C]. split. intros.
move : (B x0 b). unfold xt. move => X. Focus 2. move : (B n true). 
unfold xt. rewrite -(beq_nat_refl n). move => D. apply auxiliary3 in D.
rewrite D. auto.
move: X. case nx: (_=?_). apply beq_nat_true in nx. move: H0.
rewrite -nx. rewrite xvn. discriminate. rewrite H0. intros. apply auxiliary3 in X.
auto. 
split. intros. move:H. move => [A B].
move : (A x0 b). unfold xt. case nx: (_ =?_). apply beq_nat_true in nx.
move : H0. rewrite -nx. rewrite xvn. discriminate. rewrite H0. move => C.
apply auxiliary3 in C. auto. move: H. move => [A B]. move: (A n false).
unfold xt. rewrite -(beq_nat_refl n). move => D. apply auxiliary3 in D.
rewrite D. auto. Qed.

Lemma auxiliary2:
forall b: bool, forall a:bool, (Some b = Some b -> a = negb a) -> a = negb a.
auto. 
Qed.

(* -------------------------------------------------------------------- *)
Lemma nifForm_tauto_complete (p : nifForm) :
  nifForm_tauto p = false -> exists v, nifsem v p = false.
Proof.
induction p => //=. intros. exists (fun _ => false). auto. rewrite auxiliary. simpl.
intros.  move :H. case c2: (nifForm_tauto_r _ p2). rewrite andb_comm /=. move => H1.
apply (nifForm_tauto_r_complete _ _) in H1. destruct H1. exists x. case xn: (x n).
move :H. move => [A B]. auto.
move :H. move => [A B]. unfold xt in A. move: (A n true). rewrite -(beq_nat_refl n).
intros. rewrite xn in A0. apply auxiliary2 in A0. move: A0. simpl. discriminate. 

intros. rewrite andb_comm in H. move :H. simpl. intros. 
apply (nifForm_tauto_r_complete _ _) in c2. 
unfold xt in c2. destruct c2. exists x. case xn: (x n). move :H0.
move => [A B].  
move: (A n false). rewrite -(beq_nat_refl n).
intros. rewrite xn in A0. apply auxiliary2 in A0. move: A0. simpl. discriminate. 
move :H0. move => [A B]. auto. 
Qed.


(* -------------------------------------------------------------------- *)
(* From this, define a decision procedure for the univdesal validity    *
 * and non-normalized assertions.                                       *)


Definition is_tautology (p : prop) : bool := nifForm_tauto (norm (ifForm_of_prop p)).

(* -------------------------------------------------------------------- *)
(* Show the correctness of the procedure...                             *)


Lemma same_2 (p : prop)(v : nat -> bool): ifsem v (ifForm_of_prop p) = true -> sem v p = true.
Proof.
intros.
rewrite -ifForm_correct in H.
done.
Qed.

Lemma same_3 (p : prop)(v : nat -> bool): nifsem v (norm (ifForm_of_prop p)) = true -> ifsem v (ifForm_of_prop p) = true.
Proof.
intros.
rewrite norm_correct in H.
done.
Qed.


Lemma is_tautology_correct (p : prop) : is_tautology p = true -> valid p.
Proof.
intros.
unfold is_tautology in H.
unfold valid.
intros.
unfold sat.
apply same_2.
apply same_3.
apply nifForm_tauto_correct; done.
Qed.

(* -------------------------------------------------------------------- *)
(* ...and its completness.                                              *)
Lemma fact_1 (p : prop)(v : nat -> bool): nifsem v (norm (ifForm_of_prop p)) = false -> sem v p = false.
Proof.
intros.
rewrite norm_correct in H.
rewrite -ifForm_correct in H.
done.
Qed.

Lemma is_tautology_complete (p : prop) :
  is_tautology p = false -> exists v, sem v p = false.
Proof.
intros.
unfold is_tautology in H.
pose proof nifForm_tauto_complete as X.
destruct X with (norm (ifForm_of_prop p)); auto.
exists x.
rewrite fact_1; auto.
Qed.
