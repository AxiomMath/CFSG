module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.Lines

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem exists_complement_of_not_mem (h : Counterexample p A θ) {E : Subgroup G}
    (hE : E ∈ signalizerFunctorEk p 1 A) {a : G} (ha : a ∈ A) (haE : a ∉ E) :
    ∃ B : Subgroup G, B ≤ A ∧ Subgroup.zpowers a ≤ B ∧ E ⊓ B = ⊥ ∧ E ⊔ B = A ∧
      Nat.card B = p ^ 2 := by
  have ha1 : a ≠ 1 := fun h1 => haE (h1 ▸ E.one_mem)
  have hdisj : E ⊓ Subgroup.zpowers a = ⊥ :=
    inf_eq_bot_of_not_le h.prime (h.card_zpowers ha ha1)
      fun hle => haE (hle (Subgroup.mem_zpowers a))
  obtain ⟨B, hBA, hRB, hEB, hsup⟩ := exists_complement_containing h.prime h.elemAbelian hE.1
    (Subgroup.zpowers_le.mpr ha) hdisj
  refine ⟨B, hBA, hRB, hEB, hsup, ?_⟩
  have hcard := card_mul_card_complement h.elemAbelian hE.1 hBA hEB hsup
  rw [hE.2, h.card, pow_one] at hcard
  exact Nat.eq_of_mul_eq_mul_left h.prime.pos (hcard.trans (by ring))

omit [Finite G] in
theorem not_mem_of_mem_complement {E B : Subgroup G} (hEB : E ⊓ B = ⊥) {x : G} (hxB : x ∈ B)
    (hx1 : x ≠ 1) : x ∉ E := fun hxE =>
  hx1 (Subgroup.mem_bot.mp (hEB ▸ Subgroup.mem_inf.mpr ⟨hxE, hxB⟩))

theorem sup_zpowers_inf_complement (h : Counterexample p A θ) {E B : Subgroup G}
    (hE : E ∈ signalizerFunctorEk p 1 A) (hBA : B ≤ A) (hEB : E ⊓ B = ⊥) (hsup : E ⊔ B = A)
    {x : G} (hxB : x ∈ B) (hx1 : x ≠ 1) :
    (E ⊔ Subgroup.zpowers x) ⊓ B = Subgroup.zpowers x := by
  have hxE := not_mem_of_mem_complement hEB hxB hx1
  have hdisj : E ⊓ Subgroup.zpowers x = ⊥ :=
    inf_eq_bot_of_not_le h.prime (h.card_zpowers (hBA hxB) hx1)
      fun hle => hxE (hle (Subgroup.mem_zpowers x))
  have hS : E ⊔ Subgroup.zpowers x ∈ signalizerFunctorEk p (1 + 1) A :=
    sup_mem_Ek_succ h.elemAbelian hE (h.zpowers_mem_E1 (hBA hxB) hx1) hdisj
  obtain ⟨hS1, -⟩ := inf_complement_mem_E1 h.prime h.elemAbelian hE hBA hEB hsup hS le_sup_left
  have hle : Subgroup.zpowers x ≤ (E ⊔ Subgroup.zpowers x) ⊓ B :=
    le_inf le_sup_right (Subgroup.zpowers_le.mpr hxB)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hS1.2, h.card_zpowers (hBA hxB) hx1, pow_one]

theorem not_mem_zpowers_sup_of_mem_complement (h : Counterexample p A θ) {E B : Subgroup G}
    (hE : E ∈ signalizerFunctorEk p 1 A) (hBA : B ≤ A) (hEB : E ⊓ B = ⊥) (hsup : E ⊔ B = A)
    {a x : G} (haB : a ∈ B) (ha1 : a ≠ 1) (hxB : x ∈ B) (hxa : x ∉ Subgroup.zpowers a) :
    x ∉ Subgroup.zpowers a ⊔ E := by
  intro hx
  rw [sup_comm] at hx
  have := (h.sup_zpowers_inf_complement hE hBA hEB hsup haB ha1).le ⟨hx, hxB⟩
  exact hxa this

theorem sup_zpowers_inf_sup_zpowers (h : Counterexample p A θ) {E B : Subgroup G}
    (hE : E ∈ signalizerFunctorEk p 1 A) (hBA : B ≤ A) (hEB : E ⊓ B = ⊥) (hsup : E ⊔ B = A)
    {a b : G} (haB : a ∈ B) (ha1 : a ≠ 1) (hbB : b ∈ B) (hb1 : b ≠ 1)
    (hba : b ∉ Subgroup.zpowers a) :
    (Subgroup.zpowers a ⊔ E) ⊓ (Subgroup.zpowers b ⊔ E) = E := by
  have hplane : ∀ x ∈ B, x ≠ 1 → Subgroup.zpowers x ⊔ E ∈ signalizerFunctorEk p 2 A := by
    intro x hxB hx1
    have hxE := not_mem_of_mem_complement hEB hxB hx1
    have hdisj : Subgroup.zpowers x ⊓ E = ⊥ := by
      rw [inf_comm]
      exact inf_eq_bot_of_not_le h.prime (h.card_zpowers (hBA hxB) hx1)
        fun hle => hxE (hle (Subgroup.mem_zpowers x))
    have := sup_mem_Ek_succ h.elemAbelian hE (h.zpowers_mem_E1 (hBA hxB) hx1) (inf_comm E _ ▸ hdisj)
    rw [sup_comm] at this
    simpa using this
  have hne : Subgroup.zpowers a ⊔ E ≠ Subgroup.zpowers b ⊔ E := by
    intro heq
    have hb : b ∈ Subgroup.zpowers b ⊔ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
    rw [← heq] at hb
    exact h.not_mem_zpowers_sup_of_mem_complement hE hBA hEB hsup haB ha1 hbB hba hb
  have hE1 := h.inf_mem_E1_of_ne_E2 (hplane a haB ha1) (hplane b hbB hb1) hne
  refine (Subgroup.eq_of_le_of_card_ge (le_inf le_sup_right le_sup_right) ?_).symm
  rw [hE1.2, hE.2]

theorem zpowers_sup_eq_of_mem_complement (h : Counterexample p A θ) {B : Subgroup G}
    (hBA : B ≤ A) (hB : Nat.card B = p ^ 2) {f a' : G} (hfB : f ∈ B) (hf1 : f ≠ 1)
    (ha'B : a' ∈ B) (ha'f : a' ∉ Subgroup.zpowers f) :
    Subgroup.zpowers f ⊔ Subgroup.zpowers a' = B := by
  have ha'1 : a' ≠ 1 := fun h1 => ha'f (h1 ▸ Subgroup.one_mem _)
  have hdisj : Subgroup.zpowers f ⊓ Subgroup.zpowers a' = ⊥ :=
    inf_eq_bot_of_not_le h.prime (h.card_zpowers (hBA ha'B) ha'1)
      fun hle => ha'f (hle (Subgroup.mem_zpowers a'))
  have hle : Subgroup.zpowers f ⊔ Subgroup.zpowers a' ≤ B :=
    sup_le (Subgroup.zpowers_le.mpr hfB) (Subgroup.zpowers_le.mpr ha'B)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_sup_of_le_elemAbelian h.elemAbelian (Subgroup.zpowers_le.mpr (hBA hfB))
    (Subgroup.zpowers_le.mpr (hBA ha'B)) hdisj, h.card_zpowers (hBA hfB) hf1,
    h.card_zpowers (hBA ha'B) ha'1, hB, sq]

theorem exists_mem_complement_not_mem_zpowers (h : Counterexample p A θ) {B : Subgroup G}
    (hBA : B ≤ A) (hB : Nat.card B = p ^ 2) {f : G} (hfB : f ∈ B) (hf1 : f ≠ 1) :
    ∃ a' ∈ B, a' ∉ Subgroup.zpowers f := by
  by_contra! hcon
  have hle : B ≤ Subgroup.zpowers f := fun x hx => hcon x hx
  have := Subgroup.card_le_of_le hle
  rw [hB, h.card_zpowers (hBA hfB) hf1] at this
  have h2 : p < p ^ 2 := by nlinarith [h.prime.one_lt]
  omega

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
