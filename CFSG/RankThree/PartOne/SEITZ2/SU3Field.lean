module

public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open CFSG.ClassicalGroups.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K}

theorem mem_of_trace_mem {k : Subfield K} (hk : ∀ c ∈ k, σ c ∈ k) {l₁ l₂ ζ : K} (h₁ : l₁ ∈ k)
    (h₂ : l₂ ∈ k) (hΔ : l₁ * σ l₂ - l₂ * σ l₁ ≠ 0)
    (e₁ : l₁ * ζ + σ l₁ * σ ζ ∈ k) (e₂ : l₂ * ζ + σ l₂ * σ ζ ∈ k) : ζ ∈ k := by
  have hΔk : l₁ * σ l₂ - l₂ * σ l₁ ∈ k :=
    k.sub_mem (k.mul_mem h₁ (hk _ h₂)) (k.mul_mem h₂ (hk _ h₁))
  have hnum : (l₁ * ζ + σ l₁ * σ ζ) * σ l₂ - (l₂ * ζ + σ l₂ * σ ζ) * σ l₁ ∈ k :=
    k.sub_mem (k.mul_mem e₁ (hk _ h₂)) (k.mul_mem e₂ (hk _ h₁))
  have : ζ = ((l₁ * ζ + σ l₁ * σ ζ) * σ l₂ - (l₂ * ζ + σ l₂ * σ ζ) * σ l₁) /
      (l₁ * σ l₂ - l₂ * σ l₁) := by
    rw [eq_div_iff hΔ]
    ring
  rw [this]
  exact k.div_mem hnum hΔk

variable [CharP K 2]

omit [CharP K 2] in
theorem pairing_norm (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {i j : Fin n} (y : Fin n → K) (μ : K) :
    σ (herm σ (Pi.single i 1 + Pi.single j μ) y) * herm σ (Pi.single i 1 + Pi.single j μ) y =
      σ (y i) * y i + σ (y j) * y j * (σ μ * μ) + (σ μ * (σ (y i) * y j) +
        μ * σ (σ (y i) * y j)) := by
  rw [herm_add_left, herm_single_left, herm_single_left]
  simp only [map_one, one_mul, map_add, map_mul, hσ]
  ring

theorem exists_rational_of_norms (hσ : ∀ c, σ (σ c) = c) {k : Subfield K}
    (hk : ∀ c ∈ k, σ c ∈ k) {ω : K} (hω : ω ∈ k) (hω1 : ω ≠ 1) (hωn : σ ω * ω = 1)
    {y : Fin 3 → K} (hy0 : y ≠ 0) (hy : herm σ y y = 0)
    (H : ∀ i j : Fin 3, i ≠ j → ∀ μ : K, (μ = 1 ∨ μ = ω ∨ μ = ω ^ 2) →
      σ (herm σ (Pi.single i 1 + Pi.single j μ) y) *
        herm σ (Pi.single i 1 + Pi.single j μ) y ∈ k) :
    ∃ lam : K, lam ≠ 0 ∧ σ lam * lam ∈ k ∧ ∃ w : Fin 3 → K, (∀ i, w i ∈ k) ∧ y = lam • w := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hωn
  have hσω1 : σ ω ≠ 1 := by
    intro h
    apply hω1
    apply σ.injective
    rw [h, map_one]
  have hσωω : σ ω ≠ ω := by
    intro h
    rw [h] at hωn
    apply hω1
    have h3 : (ω - 1) ^ 2 = 0 := by linear_combination hωn + (1 - ω) * h2
    have := pow_eq_zero_iff (two_ne_zero) |>.1 h3
    linear_combination this
  have hΔ : (σ ω - 1) * σ (σ ω ^ 2 - 1) - (σ ω ^ 2 - 1) * σ (σ ω - 1) ≠ 0 := by
    have : (σ ω - 1) * σ (σ ω ^ 2 - 1) - (σ ω ^ 2 - 1) * σ (σ ω - 1) =
        (ω - 1) * (σ ω - 1) * (ω - σ ω) := by
      simp only [map_sub, map_pow, map_one, hσ]
      ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.2 hω1) (sub_ne_zero.2 hσω1))
      (sub_ne_zero.2 (Ne.symm hσωω))
  have hζ : ∀ i j : Fin 3, i ≠ j → σ (y i) * y j ∈ k := by
    intro i j hij
    set ζ := σ (y i) * y j with hζdef
    have hv : ∀ μ : K, σ μ * μ = 1 → (μ = 1 ∨ μ = ω ∨ μ = ω ^ 2) →
        σ (y i) * y i + σ (y j) * y j + (σ μ * ζ + μ * σ ζ) ∈ k := by
      intro μ hμ hμs
      have := H i j hij μ hμs
      rw [pairing_norm hσ, hμ, mul_one] at this
      exact this
    have h1 := hv 1 (by simp) (Or.inl rfl)
    have hω2 : σ (ω ^ 2) * ω ^ 2 = 1 := by rw [map_pow, ← mul_pow, hωn, one_pow]
    have e1 := hv ω hωn (Or.inr (Or.inl rfl))
    have e2 := hv (ω ^ 2) hω2 (Or.inr (Or.inr rfl))
    have d1 : (σ ω - 1) * ζ + σ (σ ω - 1) * σ ζ ∈ k := by
      have := k.sub_mem e1 h1
      convert this using 1
      simp only [map_sub, map_one, hσ]
      ring
    have d2 : (σ ω ^ 2 - 1) * ζ + σ (σ ω ^ 2 - 1) * σ ζ ∈ k := by
      have := k.sub_mem e2 h1
      convert this using 1
      simp only [map_sub, map_one, map_pow, hσ]
      ring
    refine mem_of_trace_mem hk (k.sub_mem (hk _ hω) k.one_mem)
      (k.sub_mem (k.pow_mem (hk _ hω) 2) k.one_mem) ?_ d1 ?_
    · exact hΔ
    · exact d2
  have hN : ∀ i : Fin 3, σ (y i) * y i ∈ k := by
    have hpair : ∀ i j : Fin 3, i ≠ j → σ (y i) * y i + σ (y j) * y j ∈ k := by
      intro i j hij
      have h1 := H i j hij 1 (Or.inl rfl)
      rw [pairing_norm hσ] at h1
      simp only [map_one, mul_one, one_mul] at h1
      have h3 : σ (y i) * y j + σ (σ (y i) * y j) ∈ k :=
        k.add_mem (hζ i j hij) (hk _ (hζ i j hij))
      have := k.sub_mem h1 h3
      convert this using 1
      ring
    have hy3 : σ (y 0) * y 0 + σ (y 1) * y 1 + σ (y 2) * y 2 = 0 := by
      rw [herm_def, Fin.sum_univ_three] at hy
      exact hy
    have hN0 : σ (y 0) * y 0 ∈ k := by
      have := hpair 1 2 (by decide)
      convert this using 1
      linear_combination hy3 - (σ (y 1) * y 1 + σ (y 2) * y 2) * h2
    have hN1 : σ (y 1) * y 1 ∈ k := by
      have := hpair 0 2 (by decide)
      convert this using 1
      linear_combination hy3 - (σ (y 0) * y 0 + σ (y 2) * y 2) * h2
    have hN2 : σ (y 2) * y 2 ∈ k := by
      have := hpair 0 1 (by decide)
      convert this using 1
      linear_combination hy3 - (σ (y 0) * y 0 + σ (y 1) * y 1) * h2
    intro i
    fin_cases i
    · exact hN0
    · exact hN1
    · exact hN2
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy0 (funext hcon)
  have hσi : σ (y i) ≠ 0 := (map_ne_zero σ).2 hi
  refine ⟨(σ (y i))⁻¹, inv_ne_zero hσi, ?_, σ (y i) • y, ?_, ?_⟩
  · have : σ (σ (y i))⁻¹ * (σ (y i))⁻¹ = (σ (y i) * y i)⁻¹ := by
      rw [map_inv₀, hσ]
      field_simp
    rw [this]
    exact k.inv_mem (hN i)
  · intro j
    by_cases hij : j = i
    · subst hij
      simpa using hN j
    · simpa using hζ i j (Ne.symm hij)
  · funext j
    show y j = (σ (y i))⁻¹ * (σ (y i) * y j)
    rw [← mul_assoc, inv_mul_cancel₀ hσi, one_mul]

end CFSG.RankThree.PartOne.SEITZ2
