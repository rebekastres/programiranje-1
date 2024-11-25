-- Izomorfizmi

theorem eq1 {A B : Prop} : (A ∧ B) ↔ (B ∧ A) :=
  by
    -- apply Iff.intro
    constructor
    intro ab -- dokazujemo implikacijo
    -- apply And.intro lahko bi na tak način dokazali 'in' lahko pa smo leni in dokažemo kot
    constructor
    exact ab.right -- fancy dostop do para (če ne bi morali par deconstruirat)
    exact ab.left
    -- dokazati moramo še v drugo smer
    intro ba -- podobno kot zgoraj
    sorry

theorem eq2 {A B : Prop} : (A ∨ B) ↔ (B ∨ A) :=
  sorry

theorem eq3 {A B C : Prop} : (A ∧ (B ∧ C)) ↔ (B ∧ (A ∧ C)) :=
  sorry

theorem eq4 {A B C : Prop} : (A ∨ (B ∨ C)) ↔ (B ∨ (A ∨ C)) :=
 sorry

theorem eq5 {A B C : Prop} : A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) :=
  sorry

theorem eq6 {A B C : Prop} : (B ∨ C) → A ↔ (B → A) ∧ (C → A) :=
  by
    constructor
    intro h
    constructor
    intro b
    apply h
    left
    exact b
    intro c
    have xx : B ∨ C := Or.inr c -- vložitev za ali;; znak za ali se napiše kot '\or'
    have yy := h (Or.inr c)
    exact yy -- dobimo a
    -- zdaj pa dokažimo še v drugo smer
    intro h BvC -- dokazati moramo A
    cases BvC
    case inr c =>
      exact h.right c
    case inl b => -- dokazati moramo A in vemo B
      have l := h.left
      apply h.left
      exact b

theorem eq7 {A B C : Prop} : C → (A ∧ B) ↔ (C → A) ∧ (C → B) :=
  sorry
