
section propositional

variable (P Q R : Prop)


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  := by
  intro p
  intro np
  exact np p

theorem doubleneg_elim :
  ¬¬P → P  := by
  intro nnp
  by_cases p : P
  exact p
  apply False.elim
  exact nnp p


theorem doubleneg_law :
  ¬¬P ↔ P  := by
  apply Iff.intro
  intro nnp
  exact doubleneg_elim P nnp
  intro p
  exact doubleneg_intro P p

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  := by
  intro h
  apply Or.elim h
  intro p
  apply Or.inr
  exact p
  intro q
  apply Or.inl
  exact q

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  := by
  intro peq
  apply And.intro
  exact peq.right
  exact peq.left




------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  := by
  intro h
  intro p
  apply h.elim
  intro np
  apply False.elim
  exact np p
  intro q
  exact q

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  := by
  intro h
  intro np
  apply h.elim
  intro p
  apply False.elim
  exact np p
  intro q
  exact q


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  := by
  intro h
  intro nq
  intro p
  have q := h p
  exact nq q

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  := by
  intro h
  intro p
  by_cases q : Q
  exact q
  apply False.elim
  have np := h q
  exact np p

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  := by
  apply Iff.intro
  intro pq
  exact impl_as_contrapositive P Q pq
  intro nqnp
  exact impl_as_contrapositive_converse P Q nqnp


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  := by
  intro h
  have h' : (P∨¬P) := by
    apply Or.inr
    intro p
    have h'' : (P∨¬P) := by
      apply Or.inl
      exact p
    exact h h''
  exact h h'

------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  := by
  intro h
  intro np
  have h' : (P → Q) := by
    intro p
    apply False.elim
    exact np p
  have p := h h'
  exact np p


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  := by
  intro porq
  intro h
  have np := h.left
  have nq := h.right
  apply porq.elim
  intro p
  exact np p
  intro q
  exact nq q

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  := by
  intro peq
  intro npounq
  have p := peq.left
  have q:= peq.right
  apply npounq.elim
  intro np
  exact np p
  intro nq
  exact nq q

------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  := by
  intro npouq
  apply And.intro
  intro p
  have pouq : (P∨Q) := by
    apply Or.inl
    exact p
  exact npouq pouq
  intro q
  have pouq : (P∨Q) := by
    apply Or.inr
    exact q
  exact npouq pouq

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  := by
  intro npenq
  intro pouq
  have np := npenq.left
  have nq := npenq.right
  apply pouq.elim
  exact np
  exact nq

theorem demorgan_conj : -- com lem
  ¬(P∧Q) → (¬Q ∨ ¬P)  := by
  intro npeq
  by_cases p : P
  by_cases q : Q
  have  peq : (P ∧ Q) := by
    apply And.intro
    exact p
    exact q
  apply False.elim
  exact npeq peq
  exact Or.inl q
  exact Or.inr p


theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  := by
  intro nqounp
  intro peq
  apply nqounp.elim
  have q := peq.right
  intro nq
  exact nq q
  have p := peq.left
  intro np
  exact np p

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  := by
  apply Iff.intro
  exact demorgan_conj P Q
  exact demorgan_conj_converse P Q

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  := by
  apply Iff.intro
  exact demorgan_disj P Q
  exact demorgan_disj_converse P Q

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  := by
  intro h
  have p := h.left
  have qour := h.right
  apply qour.elim
  intro q
  apply Or.inl
  apply And.intro
  exact p
  exact q
  intro r
  apply Or.inr
  apply And.intro
  exact p
  exact r

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  := by
  intro h
  apply h.elim
  intro peq
  apply And.intro
  exact peq.left
  apply Or.inl
  exact peq.right
  intro per
  apply And.intro
  exact per.left
  apply Or.inr
  exact per.right

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  := by
  intro h
  apply And.intro
  apply h.elim
  intro p
  exact Or.inl p
  intro qer
  exact Or.inr qer.left
  apply h.elim
  intro p
  exact Or.inl p
  intro qer
  exact Or.inr qer.right

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  := by
  intro h
  have pouq := h.left
  apply pouq.elim
  intro p
  exact Or.inl p
  intro q
  have pour := h.right
  apply pour.elim
  intro p
  exact Or.inl p
  intro r
  apply Or.inr
  apply And.intro
  exact q
  exact r


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  := by
  intro h
  intro p
  intro q
  have peq : (P ∧ Q) := by
    apply And.intro
    exact p
    exact q
  exact h peq

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  := by
  intro h
  intro peq
  exact h peq.left peq.right

------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  := by
  intro p
  exact p

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  := by
  intro p
  apply Or.inl
  exact p

theorem weaken_disj_left :
  Q → (P∨Q)  := by
  intro q
  apply Or.inr
  exact q

theorem weaken_conj_right :
  (P∧Q) → P  := by
  intro peq
  exact peq.left

theorem weaken_conj_left :
  (P∧Q) → Q  := by
  intro peq
  exact peq.right

theorem conj_idempot :
  (P∧P) ↔ P := by
  apply Iff.intro
  intro pep
  exact pep.left
  intro p
  apply And.intro
  exact p
  exact p

theorem disj_idempot :
  (P∨P) ↔ P  := by
  apply Iff.intro
  intro poup
  apply poup.elim
  exact impl_refl P
  exact impl_refl P
  exact weaken_disj_right P P

end propositional


----------------------------------------------------------------


section predicate

variable (U : Type)
variable (P Q : U -> Prop)


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  := by
  intro h
  intro x
  intro px
  apply h
  exact Exists.intro x px

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  := by
  intro h
  intro ex
  apply Exists.elim ex
  intro a
  intro pa
  have npa := h a
  exact npa pa

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  := by
  intro h
  apply Classical.byContradiction
  intro nex
  apply h
  intro x
  by_cases px : P x
  exact px
  apply False.elim
  apply nex
  exact Exists.intro x px

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  := by
  intro he
  intro hfa
  apply Exists.elim he
  intro a npa
  have pa := hfa a
  exact npa pa

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  := by
  apply Iff.intro
  exact demorgan_forall U P
  exact demorgan_forall_converse U P

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  := by
  apply Iff.intro
  exact demorgan_exists U P
  exact demorgan_exists_converse U P

------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  := by
  intro he
  intro hfa
  apply Exists.elim he
  intro a pa
  have npa := hfa a
  exact npa pa

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  := by
  intro hfa
  intro he
  apply Exists.elim he
  intro a npa
  have pa := hfa a
  exact npa pa

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  := by
  intro nhe
  intro x
  by_cases px : P x
  exact px
  apply False.elim
  apply nhe
  exact Exists.intro x px

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  := by
  intro hnfa
  apply Classical.byContradiction
  intro nhe
  apply hnfa
  intro x
  intro px
  apply nhe
  exact Exists.intro x px

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  := by
  apply Iff.intro
  exact forall_as_neg_exists U P
  exact forall_as_neg_exists_converse U P

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  := by
  apply Iff.intro
  exact exists_as_neg_forall U P
  exact exists_as_neg_forall_converse U P


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  := by
  intro he
  apply Exists.elim he
  intro x pxeqx
  apply And.intro
  exact Exists.intro x pxeqx.left
  exact Exists.intro x pxeqx.right

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  := by
  intro he
  apply Exists.elim he
  intro x pxouqx
  apply pxouqx.elim
  intro px
  apply Or.inl
  exact Exists.intro x px
  intro qx
  apply Or.inr
  exact Exists.intro x qx

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  := by
  intro hde
  apply hde.elim
  intro hep
  apply Exists.elim hep
  intro x px
  apply Exists.intro x
  apply Or.inl
  exact px
  intro heq
  apply Exists.elim heq
  intro x qx
  apply Exists.intro x
  apply Or.inr
  exact qx

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  := by
  intro hfa
  apply And.intro
  intro x
  have pxeqx := hfa x
  exact pxeqx.left
  intro x
  have pxeqx := hfa x
  exact pxeqx.right

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  := by
  intro h
  intro x
  apply And.intro
  exact h.left x
  exact h.right x

theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  := by
  intro h
  apply h.elim
  intro hpx
  intro x
  apply Or.inl
  exact hpx x
  intro hqx
  intro x
  apply Or.inr
  exact hqx x

/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
