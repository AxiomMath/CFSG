module

public import CFSG.Quasithin.Vol2.KGFact12618e

public section

namespace CFSG.Quasithin.H13.KG12618

open Equiv

theorem eq_one_or_swap_of_commute_c3_eight (σ : Perm (Fin 8))
    (h₁ : σ * (swap 0 2 * swap 0 1) = (swap 0 2 * swap 0 1) * σ)
    (h₂ : σ * (swap 2 4 * swap 2 3) = (swap 2 4 * swap 2 3) * σ)
    (h₃ : σ * (swap 4 0 * swap 4 5) = (swap 4 0 * swap 4 5) * σ) :
    σ = 1 ∨ σ = swap 6 7 := by
  set c₁ : Perm (Fin 8) := swap 0 2 * swap 0 1 with hc₁
  set c₂ : Perm (Fin 8) := swap 2 4 * swap 2 3 with hc₂
  set c₃ : Perm (Fin 8) := swap 4 0 * swap 4 5 with hc₃
  have e₁ : ∀ x, σ (c₁ x) = c₁ (σ x) := fun x => by
    simpa [Perm.mul_apply] using congrArg (fun τ : Perm (Fin 8) => τ x) h₁
  have e₂ : ∀ x, σ (c₂ x) = c₂ (σ x) := fun x => by
    simpa [Perm.mul_apply] using congrArg (fun τ : Perm (Fin 8) => τ x) h₂
  have e₃ : ∀ x, σ (c₃ x) = c₃ (σ x) := fun x => by
    simpa [Perm.mul_apply] using congrArg (fun τ : Perm (Fin 8) => τ x) h₃
  have s1 : σ 1 = c₁ (σ 0) := by rw [← e₁]; rfl
  have s2 : σ 2 = c₁ (σ 1) := by rw [← e₁]; rfl
  have s3 : σ 3 = c₂ (σ 2) := by rw [← e₂]; rfl
  have s4 : σ 4 = c₂ (σ 3) := by rw [← e₂]; rfl
  have s4' : σ 4 = c₃ (σ 0) := by rw [← e₃]; rfl
  have s5 : σ 5 = c₃ (σ 4) := by rw [← e₃]; rfl
  have h10 : σ 1 ≠ σ 0 := fun h => absurd (σ.injective h) (by decide)
  have key : ∀ a : Fin 8, c₁ a ≠ a → c₃ a = c₂ (c₂ (c₁ (c₁ a))) → a = 0 := by
    rw [hc₁, hc₂, hc₃]
    decide
  have h0 : σ 0 = 0 := key (σ 0) (by rw [← s1]; exact h10) (by rw [← s4', s4, s3, s2, s1])
  have f1 : σ 1 = 1 := by rw [s1, h0, hc₁]; decide
  have f2 : σ 2 = 2 := by rw [s2, f1, hc₁]; decide
  have f3 : σ 3 = 3 := by rw [s3, f2, hc₂]; decide
  have f4 : σ 4 = 4 := by rw [s4', h0, hc₃]; decide
  have f5 : σ 5 = 5 := by rw [s5, f4, hc₃]; decide
  have hfix : ∀ i : Fin 8, i ≠ 6 → i ≠ 7 → σ i = i := by
    intro i hi6 hi7
    fin_cases i
    · exact h0
    · exact f1
    · exact f2
    · exact f3
    · exact f4
    · exact f5
    · exact absurd rfl hi6
    · exact absurd rfl hi7
  have hin : ∀ j : Fin 8, (j = 6 ∨ j = 7) → σ j = 6 ∨ σ j = 7 := by
    intro j hj
    by_contra h
    push Not at h
    have h1 := hfix (σ j) h.1 h.2
    have h2 := σ.injective h1
    rw [h2] at h
    rcases hj with rfl | rfl
    · exact h.1 rfl
    · exact h.2 rfl
  rcases hin 6 (Or.inl rfl) with h6 | h6
  · left
    have h7 : σ 7 = 7 := by
      rcases hin 7 (Or.inr rfl) with h | h
      · exact absurd (σ.injective (h.trans h6.symm)) (by decide)
      · exact h
    ext i
    by_cases hi6 : i = 6
    · rw [hi6, h6]; rfl
    by_cases hi7 : i = 7
    · rw [hi7, h7]; rfl
    rw [hfix i hi6 hi7]; rfl
  · right
    have h7 : σ 7 = 6 := by
      rcases hin 7 (Or.inr rfl) with h | h
      · exact h
      · exact absurd (σ.injective (h.trans h6.symm)) (by decide)
    ext i
    by_cases hi6 : i = 6
    · rw [hi6, h6]; rfl
    by_cases hi7 : i = 7
    · rw [hi7, h7]; rfl
    rw [hfix i hi6 hi7, swap_apply_of_ne_of_ne hi6 hi7]

theorem conj_stab8 (g : Perm (Fin 8)) (p q : Fin 8) :
    (stab8 p q).map (MulAut.conj g).toMonoidHom = stab8 (g p) (g q) := by
  ext σ
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mem_stab8]
  constructor
  · rintro ⟨τ, ⟨hτA, hτp, hτq⟩, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Perm.mem_alternatingGroup] at hτA ⊢
      simp only [Perm.sign_mul, Perm.sign_inv, hτA, mul_one]
      exact Int.units_mul_self _
    · simp [Perm.mul_apply, hτp]
    · simp [Perm.mul_apply, hτq]
  · rintro ⟨hσA, hσp, hσq⟩
    refine ⟨g⁻¹ * σ * g, ⟨?_, ?_, ?_⟩, by group⟩
    · rw [Perm.mem_alternatingGroup] at hσA ⊢
      simp only [Perm.sign_mul, Perm.sign_inv, hσA, mul_one]
      exact Int.units_mul_self _
    · simp [Perm.mul_apply, hσp]
    · simp [Perm.mul_apply, hσq]

theorem eq_one_or_swap_of_commute_stab8 {p q : Fin 8} (hpq : p ≠ q) {σ : Perm (Fin 8)}
    (h : ∀ τ ∈ stab8 p q, σ * τ = τ * σ) : σ = 1 ∨ σ = swap p q := by
  set r := swap 6 p q with hr
  set g : Perm (Fin 8) := swap 6 p * swap 7 r with hg
  have hr6 : r ≠ 6 := by
    intro h
    apply hpq
    have : swap 6 p q = swap 6 p p := by rw [← hr, h, swap_apply_right]
    exact ((swap 6 p).injective this).symm
  have hg6 : g 6 = p := by
    rw [hg, Perm.mul_apply, swap_apply_of_ne_of_ne (by decide) (Ne.symm hr6), swap_apply_left]
  have hg7 : g 7 = q := by
    rw [hg, Perm.mul_apply, swap_apply_left, hr, swap_apply_self]
  have hmem : ∀ τ ∈ stab8 6 7, g * τ * g⁻¹ ∈ stab8 p q := by
    intro τ hτ
    rw [← hg6, ← hg7, ← conj_stab8]
    exact ⟨τ, hτ, rfl⟩
  have hc : ∀ τ ∈ stab8 6 7, (g⁻¹ * σ * g) * τ = τ * (g⁻¹ * σ * g) := by
    intro τ hτ
    have h1 := h _ (hmem τ hτ)
    calc (g⁻¹ * σ * g) * τ = g⁻¹ * (σ * (g * τ * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * τ * g⁻¹) * σ) * g := by rw [h1]
      _ = τ * (g⁻¹ * σ * g) := by group
  have hc₁ : swap (0 : Fin 8) 2 * swap 0 1 ∈ stab8 6 7 :=
    mem_stab8.2 ⟨Perm.mem_alternatingGroup.2 (by decide), by decide, by decide⟩
  have hc₂ : swap (2 : Fin 8) 4 * swap 2 3 ∈ stab8 6 7 :=
    mem_stab8.2 ⟨Perm.mem_alternatingGroup.2 (by decide), by decide, by decide⟩
  have hc₃ : swap (4 : Fin 8) 0 * swap 4 5 ∈ stab8 6 7 :=
    mem_stab8.2 ⟨Perm.mem_alternatingGroup.2 (by decide), by decide, by decide⟩
  rcases eq_one_or_swap_of_commute_c3_eight (g⁻¹ * σ * g) (hc _ hc₁) (hc _ hc₂) (hc _ hc₃)
    with h1 | h1
  · left
    calc σ = g * (g⁻¹ * σ * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · right
    calc σ = g * (g⁻¹ * σ * g) * g⁻¹ := by group
      _ = g * swap 6 7 * g⁻¹ := by rw [h1]
      _ = swap p q := by rw [← swap_apply_apply, hg6, hg7]

end CFSG.Quasithin.H13.KG12618
