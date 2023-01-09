
Declare Scope logic_scope.
Open Scope logic_scope.

Definition bot := forall A : Type, A.
Notation "⊥" := (bot) (at level 37) : logic_scope.

Lemma bot_elim : forall A : Type, ⊥ -> A.
Proof. intros A Hbot; apply Hbot. Qed.

Definition not : forall (A : Type), Type :=
  fun A => A -> ⊥.
Notation "¬ x" := (not x) (at level 40) : logic_scope.

Lemma bot_intro : forall A : Type, A -> ¬ A -> ⊥.
Proof. intros A a na; apply na. assumption. Qed.

Definition conj : forall (A B : Type), Type :=
  fun A B => forall C : Type, (A -> B -> C) -> C.
Notation "x ∧ y" := (conj x y) (at level 50, left associativity) : logic_scope.

Lemma conj_intro : forall A B : Type, A -> B -> A ∧ B.
Proof. intros A B a b C Hconj; apply Hconj; assumption. Qed.

Lemma conj_elim1 : forall A B : Type, A ∧ B -> A.
Proof. intros A B HAB; apply HAB; intros; assumption. Qed.

Lemma conj_elim2 : forall A B : Type, A ∧ B -> B.
Proof. intros A B HAB; apply HAB; intros; assumption. Qed.

Definition disj : forall (A B : Type), Type :=
  fun A B => forall C : Type, (A -> C) -> (B -> C) -> C.
Notation "x ∨ y" := (disj x y) (at level 53, left associativity) : logic_scope.

Lemma disj_intro1 : forall A B : Type, A ->  A ∨ B.
Proof. intros A B a C Ha _; apply Ha; assumption. Qed.

Lemma disj_intro2 : forall A B : Type, B ->  A ∨ B.
Proof. intros A B b C _ Hb; apply Hb; assumption. Qed.

Lemma disj_elim : forall A B C : Type, (A -> C) -> (B -> C) ->  A ∨ B -> C.
Proof. intros A B C HA HB HAB; apply HAB; assumption. Qed.

Definition ex : forall {S : Type} (P : S -> Type), Type :=
  fun {S} P => forall A : Type, (forall x : S, P x -> A) -> A.
Notation "∃ x .. y , P" := (ex (fun x => .. (ex (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∃  x  ..  y ']' ,  '/' P ']'") : logic_scope.

Lemma ex_elim : forall {S : Type} (P : S -> Type) (A : Type),
    (forall x : S, P x -> A) -> (∃ x : S, P x) -> A.
Proof. intros * Hall Hex; apply Hex; assumption. Qed.

Lemma ex_intro : forall {S : Type} (P : S -> Type) (a : S), P a -> ∃ x : S, P x.
Proof. intros * Ha A Hall; apply Hall with a; assumption. Qed.

Definition iff : forall (A B : Type), Type :=
  fun A B => (A -> B) ∧ (B -> A).
Notation "x ↔ y" := (iff x y) (at level 57, no associativity) : logic_scope.

