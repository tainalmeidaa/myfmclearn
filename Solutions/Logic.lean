section propositional

variable (P Q R : Prop)

------------------------------------------------
-- Double negation
------------------------------------------------

theorem doubleneg_intro :
  P → ¬ ¬ P  := by
  intro p
  intro np
  contradiction

theorem doubleneg_elim :
  ¬ ¬ P → P  := by
  intro nnp
  by_cases h : P
  exact h
  contradiction

theorem doubleneg_law :
  ¬ ¬ P ↔ P  := by
  constructor
  intro (nnp : ¬ ¬ P)
  by_cases h : P
  exact h
  contradiction
  intro (hp : P)
  intro (np : ¬ P)
  contradiction

------------------------------------------------
-- Commutativity of ∨,∧
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  := by

  intro (hpq: (P ∨ Q))
  rcases hpq with (hp | hq)
  -- caso P
  right; exact hp
  -- caso Q
  left; exact hq

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  := by
  intro (hpq : (P ∧ Q))
  rcases hpq with ⟨ hp , hq ⟩
  constructor
  exact hq
  exact hp

------------------------------------------------
-- Interdefinability of →,∨
------------------------------------------------

theorem impl_as_disj_converse :
  (¬ P ∨ Q) → (P → Q)  := by
  intro (hpq : (¬ P ∨ Q))
  intro (hip: P)
  rcases hpq with (hp | hq)
  contradiction
  exact hq


theorem disj_as_impl :
  (P ∨ Q) → (¬ P → Q)  := by
  intro (hpq : P ∨ Q)
  intro (np : ¬ P)
  rcases hpq with (hp | hq)
  contradiction
  exact hq

------------------------------------------------
-- Contrapositive
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬ Q → ¬ P)  := by
  intro (hpq : (P → Q))
  by_cases h : P
  have hq : Q := hpq h -- aplicando P → Q em P
  intro (nq : ¬ Q)
  contradiction
  intro (np' : ¬ Q)
  exact h


theorem impl_as_contrapositive_converse :
  (¬ Q → ¬ P) → (P → Q)  := by
  intro (npq : (¬ Q → ¬ P))
  by_cases hq : Q
  intro (hp : P)
  exact hq
  intro (hip : P)
  have np : ¬ P :=  npq hq
  contradiction

theorem contrapositive_law :
  (P → Q) ↔ (¬ Q → ¬ P)  := by
  constructor
  -- caso (P → Q) → (¬ Q → ¬ P)
  intro (hpq : P → Q)
  intro (nq : ¬ Q)
  intro (hp : P)
  have hq : Q := hpq hp
  contradiction

  -- caso (P → Q) ← (¬ Q → ¬ P)
  intro (nqp : ¬Q → ¬P)
  intro (p : P)
  by_cases q : Q
    -- caso Q
  exact q
    -- caso ¬ Q
  have np : ¬ P := nqp q
  contradiction

------------------------------------------------
-- Irrefutability of LEM[P]
------------------------------------------------

theorem lem_irrefutable :
  ¬ ¬ (P ∨ ¬ P)  := by

intro (hpp : ¬ (P ∨ ¬ P))
by_cases h : P ;

-- caso P
   -- vou demonstrar pp
have pp : (P ∨ ¬ P) := by{
left; exact h
};

contradiction

  -- vou demonstrar hpp
have npp : ¬ (P ∨ ¬ P) := by{
exact hpp
};

-- caso não P
have z : (P ∨ ¬ P) := by{
right; exact h
};

contradiction

-- OBS : não devo usar magia aqui(?) preciso refazer

------------------------------------------------
-- Peirce's law
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬ ¬ P  := by
  intro (h1 : ((P → Q) → P))
  intro (h2: ¬ P)
  -- vou demonstrar (P → Q):
  have h3 : (P → Q) := by {
    intro (h3': P)
    contradiction
  }
  have h4 : P := h1 h3 --- apliquei h1 : (P → Q) → P em h3 : (P → Q) para obter P
  contradiction

------------------------------------------------
-- Linearity of →
------------------------------------------------

theorem impl_linear :
  (P → Q) ∨ (Q → P)  := by

  by_cases hp : P
  right;
  intro (q : Q)
  exact hp
  left;
  intro (p : P)
  contradiction


------------------------------------------------
-- Interdefinability of ∨,∧
------------------------------------------------

theorem disj_as_negconj :
  P ∨ Q → ¬ (¬ P ∧ ¬ Q)  := by

  intro (hpq : P ∨ Q)
  intro (npq : ¬ P ∧ ¬ Q)
  rcases hpq with (hp|hq)
  -- case inl
  rcases npq with ⟨hp , hq⟩
  contradiction
  -- case inr
  rcases npq with ⟨np , nq⟩
  contradiction


theorem conj_as_negdisj :
  P ∧ Q → ¬ (¬ P ∨ ¬ Q)  := by
  intro (hpq : P ∧ Q)
  intro (npq : ¬ P ∨ ¬ Q)
  rcases npq with (np|nq)
  --case inl
  rcases hpq with ⟨hp , hq⟩
  contradiction
  --case inr
  rcases hpq with ⟨hp', hq'⟩
  contradiction


------------------------------------------------
-- De Morgan laws for ∨,∧
------------------------------------------------

theorem demorgan_disj :
  ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)  := by

  intro (h : ¬ (P ∨ Q))
  constructor
  -- parte não P
  intro (p : P)
  have h' : (P ∨ Q) := by {
    left;
    exact p;
  };

  contradiction

  -- parte não q
  intro (q : Q)
  have h' : (P ∨ Q) := by {
    right;
    exact q;
  };

  contradiction



theorem demorgan_disj_converse :
  (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)  := by

  intro (h : (¬ P ∧ ¬ Q))
  intro (h': P ∨ Q)
  -- separo em casos P ∨ Q
  rcases h' with (hp | hq)
  -- extraio L
  rcases h with ⟨hp , hq⟩
  contradiction
  -- extraio R
  rcases h with ⟨hp , hq⟩
  contradiction


theorem demorgan_conj :
  ¬ (P ∧ Q) → (¬ Q ∨ ¬ P)  := by

  sorry


theorem demorgan_conj_converse :
  (¬ Q ∨ ¬ P) → ¬ (P ∧ Q)  := by

  intro (npq: (¬ Q ∨ ¬ P))
  intro (npq': P ∧ Q)
  rcases npq with (np | nq)
  -- caso não Q
  rcases npq' with ⟨p , q⟩
  contradiction
  -- caso não P
  rcases npq' with ⟨p , q⟩
  contradiction


theorem demorgan_conj_law :
  ¬ (P ∧ Q) ↔ (¬ Q ∨ ¬ P)  := by
  sorry

theorem demorgan_disj_law :
  ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)  := by
  sorry


------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

theorem distr_conj_disj :
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  := by

  intro (h : P ∧ (Q ∨ R))
  left;
  constructor
  -- caso L
  rcases h with ⟨h1,h2⟩
  exact h1
  --caso R
  rcases h with ⟨h1,h2⟩
  rcases h2 with (h1'|h2')
  -- case h.right.intro.inl
  exact h1'
  -- case h.right.intro.inr
  sorry



theorem distr_conj_disj_converse :
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  := by
  sorry

theorem distr_disj_conj :
  P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  := by
  sorry

theorem distr_disj_conj_converse :
  (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  := by
  sorry


------------------------------------------------
-- Currying
------------------------------------------------

theorem curry_prop :
  ((P ∧ Q) → R) → (P → (Q → R))  := by
  intro (h : ((P ∧ Q) → R))
  intro (hp : P)
  intro (hq : Q)
  -- vou demonstrar P ∧ Q
  have hpq : (P ∧ Q) := by{
    constructor
    --caso L
    exact hp
    --caso R
    exact hq
  };
  have hr : R := h hpq -- aplicar para obter
  exact hr;


theorem uncurry_prop :
  (P → (Q → R)) → ((P ∧ Q) → R)  := by
  intro (h : (P → (Q → R)))
  intro (hpq : (P ∧ Q))
  rcases hpq with ⟨hp,hq⟩
  have hr: R := h hp hq
  exact hr;

------------------------------------------------
-- Reflexivity of →
------------------------------------------------

theorem impl_refl :
  P → P  := by
  intro (hp : P)
  exact hp;

------------------------------------------------
-- Weakening and contraction
------------------------------------------------

theorem weaken_disj_right :
  P → (P ∨ Q)  := by
  intro (h : P)
  left;
  exact h;

theorem weaken_disj_left :
  Q → (P ∨ Q)  := by
  intro (h : Q)
  right;
  exact h;

theorem weaken_conj_right :
  (P ∧ Q) → P  := by
  intro (hpq : P ∧ Q)
  rcases hpq with ⟨hp , hq⟩
  exact hp;

theorem weaken_conj_left :
  (P ∧ Q) → Q  := by
  intro (hpq : P ∧ Q)
  rcases hpq with ⟨hp , hq⟩
  exact hq;



------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem :
  (P ∨ P) ↔ P  := by
  constructor
  -- caso (P ∨ P) → P
  intro (hp : (P ∨ P))
  rcases hp with (hp1 | hp2)
    -- caso P
  exact hp1;
    --caso P
  exact hp2;

  -- caso P → (P ∨ P)
  intro (hp': P)
  left;
  exact hp';


theorem conj_idem :
  (P ∧ P) ↔ P := by
  constructor
  -- caso (P ∧ P) → P
  intro (hp : (P ∧ P));
  rcases hp with ⟨hp1 , hp2⟩
  exact hp1;
  -- caso P → (P ∧ P)
  intro (hp' : P)
  constructor
  -- caso L
  exact hp';
  --caso R
  exact hp';


------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom :
  False → P := by
  sorry

theorem true_top :
  P → True  := by
  sorry


end propositional

----------------------------------------------------------------

section predicate

variable (U : Type)
variable (P Q : U → Type)


------------------------------------------------
-- De Morgan laws for ∃,∀
------------------------------------------------

theorem demorgan_exists :
  ¬ (∃ x, P x) → (∀ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_converse :
  (∀ x, ¬ P x) → ¬ (∃ x, P x)  := by
  sorry

theorem demorgan_forall :
  ¬ (∀ x, P x) → (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_forall_converse :
  (∃ x, ¬ P x) → ¬ (∀ x, P x)  := by
  sorry

theorem demorgan_forall_law :
  ¬ (∀ x, P x) ↔ (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_law :
  ¬ (∃ x, P x) ↔ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
-- Interdefinability of ∃,∀
------------------------------------------------

theorem exists_as_neg_forall :
  (∃ x, P x) → ¬ (∀ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists :
  (∀ x, P x) → ¬ (∃ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists_converse :
  ¬ (∃ x, ¬ P x) → (∀ x, P x)  := by
  sorry

theorem exists_as_neg_forall_converse :
  ¬ (∀ x, ¬ P x) → (∃ x, P x)  := by
  sorry

theorem forall_as_neg_exists_law :
  (∀ x, P x) ↔ ¬ (∃ x, ¬ P x)  := by
  sorry

theorem exists_as_neg_forall_law :
  (∃ x, P x) ↔ ¬ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
--  Distributivity between quantifiers
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists :
  (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists_converse :
  (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x)  := by
  sorry

theorem forall_conj_as_conj_forall :
  (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)  := by
  sorry

theorem forall_conj_as_conj_forall_converse :
  (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)  := by
  sorry

theorem forall_disj_as_disj_forall_converse :
  (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x)  := by
  sorry


end predicate

------------------------------------------------

section bonus

------------------------------------------------
--  Drinker's paradox
------------------------------------------------

variable (D : U → Prop)

-- There is a person p such that:
-- if p drinks, then everybody drinks
-- p: «person»
-- D x: «x drinks»
theorem drinker :
  ∃ p, (D p → ∀ x, D x)  := by
  sorry

------------------------------------------------
--  Russell's paradox
------------------------------------------------

variable (S : U → U → Prop)

-- It is impossible to have a barber b such that
-- b shaves exactly those people who do not shave themselves
-- b: «barber»
-- S x y: «x shaves y»
theorem russell :
  ¬ ∃ b, ∀ x, (S b x ↔ ¬ S x x)  := by
  sorry


end bonus


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)  := by
  sorry

theorem exists_conj_as_conj_exists_converse :
  (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)  := by
  sorry

---------------------------------------------- -/
