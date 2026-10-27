module

public import CFSG.RankThree.PartOne.SEITZ2.SU3Field

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open CFSG.ClassicalGroups.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K} [CharP K 2]

theorem zeta_mem {n : ℕ} (hσ : ∀ c, σ (σ c) = c) {k : Subfield K} (hk : ∀ c ∈ k, σ c ∈ k)
    {ω : K} (hω : ω ∈ k) (hω1 : ω ≠ 1) (hωn : σ ω * ω = 1) {y : Fin n → K}
    (H : ∀ i j : Fin n, i ≠ j → ∀ μ : K, (μ = 1 ∨ μ = ω ∨ μ = ω ^ 2) →
      σ (herm σ (Pi.single i 1 + Pi.single j μ) y) *
        herm σ (Pi.single i 1 + Pi.single j μ) y ∈ k) {i j : Fin n} (hij : i ≠ j) :
    σ (y i) * y j ∈ k := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
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
  exact mem_of_trace_mem hk (k.sub_mem (hk _ hω) k.one_mem)
    (k.sub_mem (k.pow_mem (hk _ hω) 2) k.one_mem) hΔ d1 d2

theorem norm_add_mem {n : ℕ} (hσ : ∀ c, σ (σ c) = c) {k : Subfield K} (hk : ∀ c ∈ k, σ c ∈ k)
    {ω : K} (hω : ω ∈ k) (hω1 : ω ≠ 1) (hωn : σ ω * ω = 1) {y : Fin n → K}
    (H : ∀ i j : Fin n, i ≠ j → ∀ μ : K, (μ = 1 ∨ μ = ω ∨ μ = ω ^ 2) →
      σ (herm σ (Pi.single i 1 + Pi.single j μ) y) *
        herm σ (Pi.single i 1 + Pi.single j μ) y ∈ k) {i j : Fin n} (hij : i ≠ j) :
    σ (y i) * y i + σ (y j) * y j ∈ k := by
  have h1 := H i j hij 1 (Or.inl rfl)
  rw [pairing_norm hσ] at h1
  simp only [map_one, mul_one, one_mul] at h1
  have hζ := zeta_mem hσ hk hω hω1 hωn H hij
  have h3 : σ (y i) * y j + σ (σ (y i) * y j) ∈ k := k.add_mem hζ (hk _ hζ)
  have := k.sub_mem h1 h3
  convert this using 1
  ring

theorem exists_rational_of_norms_n {n : ℕ} (hσ : ∀ c, σ (σ c) = c) {k : Subfield K}
    (hk : ∀ c ∈ k, σ c ∈ k) {ω : K} (hω : ω ∈ k) (hω1 : ω ≠ 1) (hωn : σ ω * ω = 1)
    (hquad : ∀ z s t : K, σ z = z → s ∈ k → t ∈ k → σ s = s → σ t = t → z ^ 2 + s * z + t = 0 →
      z ∈ k)
    {y : Fin n → K} (hy0 : y ≠ 0) (hy : herm σ y y = 0)
    (H : ∀ i j : Fin n, i ≠ j → ∀ μ : K, (μ = 1 ∨ μ = ω ∨ μ = ω ^ 2) →
      σ (herm σ (Pi.single i 1 + Pi.single j μ) y) *
        herm σ (Pi.single i 1 + Pi.single j μ) y ∈ k) :
    ∃ lam : K, lam ≠ 0 ∧ σ lam * lam ∈ k ∧ ∃ w : Fin n → K, (∀ i, w i ∈ k) ∧ y = lam • w := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hnorm_fix : ∀ i, σ (σ (y i) * y i) = σ (y i) * y i := fun i => by
    rw [map_mul, hσ, mul_comm]
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy0 (funext hcon)
  have hσi : σ (y i) ≠ 0 := (map_ne_zero σ).2 hi
  have hNi0 : σ (y i) * y i ≠ 0 := mul_ne_zero hσi hi
  obtain ⟨j, hji, hNj⟩ : ∃ j, j ≠ i ∧ σ (y j) * y j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hNi0
    have : herm σ y y = σ (y i) * y i := by
      rw [herm_def]
      refine Finset.sum_eq_single i (fun l _ hl => hcon l hl)
        (fun h => absurd (Finset.mem_univ i) h)
    rw [← this, hy]
  have hN : σ (y i) * y i ∈ k := by
    have hs := norm_add_mem hσ hk hω hω1 hωn H (Ne.symm hji)
    have hζ := zeta_mem hσ hk hω hω1 hωn H (Ne.symm hji)
    refine hquad (σ (y i) * y i) (σ (y i) * y i + σ (y j) * y j)
      (σ (y i) * y i * (σ (y j) * y j)) (hnorm_fix i) hs ?_ ?_ ?_ ?_
    · have : σ (y i) * y i * (σ (y j) * y j) = (σ (y i) * y j) * σ (σ (y i) * y j) := by
        simp only [map_mul, hσ]
        ring
      rw [this]
      exact k.mul_mem hζ (hk _ hζ)
    · rw [map_add, hnorm_fix, hnorm_fix]
    · rw [map_mul, hnorm_fix, hnorm_fix]
    · linear_combination (σ (y i) * y i) ^ 2 * h2 + σ (y i) * y i * (σ (y j) * y j) * h2
  refine ⟨(σ (y i))⁻¹, inv_ne_zero hσi, ?_, σ (y i) • y, ?_, ?_⟩
  · have : σ (σ (y i))⁻¹ * (σ (y i))⁻¹ = (σ (y i) * y i)⁻¹ := by
      rw [map_inv₀, hσ]
      field_simp
    rw [this]
    exact k.inv_mem hN
  · intro l
    by_cases hli : l = i
    · subst hli
      simpa using hN
    · simpa using zeta_mem hσ hk hω hω1 hωn H (Ne.symm hli)
  · funext l
    show y l = (σ (y i))⁻¹ * (σ (y i) * y l)
    rw [← mul_assoc, inv_mul_cancel₀ hσi, one_mul]

end CFSG.RankThree.PartOne.SEITZ2
