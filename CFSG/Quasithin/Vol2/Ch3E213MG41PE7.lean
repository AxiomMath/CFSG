module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PE6

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp)

variable {k : Type} [Field k] [CharP k 2] {G₀ : Subgroup (antiSp k)}

omit [CharP k 2] in
theorem IPL.ratio_trans {a₁ a₂ a₃ m₁ m₂ m₃ : k} (hm₃ : m₃ ≠ 0)
    (e₁ : (1 + a₁) * m₃ = (1 + a₃) * m₁) (e₂ : (1 + a₂) * m₃ = (1 + a₃) * m₂) :
    (1 + a₁) * m₂ = (1 + a₂) * m₁ :=
  mul_right_cancel₀ hm₃ (by linear_combination m₂ * e₁ - m₁ * e₂)

theorem ratio_eq_of_three [Finite k] (hS : SectionSplit G₀) (hone : Refl.OnePerCentre G₀)
    (hirr : IsIrreducibleSp4 (Subgroup.closure (transvSet G₀))) {r s : Fin 4 → k}
    (hr : r ∈ Refl.normC G₀) (hs : s ∈ Refl.normC G₀) (hc0 : spBil r s ≠ 0)
    (hc1 : spBil r s ≠ 1) {a b : k} (hq : a ^ 2 + b ^ 2 + spBil r s * a * b ≠ 0)
    {ρ₀ : Fin 4 → k} (hρ₀P : ρ₀ = a • r + b • s) (hρ₀ : ρ₀ ∈ Refl.normC G₀) {y : Fin 4 → k}
    (hy : y ≠ 0) (hyr : spBil y r = 0) (hys : spBil y s = 0) {a₁ a₂ a₃ m₁ m₂ m₃ : k}
    (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) (hm₃ : m₃ ≠ 0) (h₁₂ : m₁ ≠ m₂) (h₁₃ : m₁ ≠ m₃)
    (h₂₃ : m₂ ≠ m₃) (hz₁ : a₁ • ρ₀ + m₁ • y ∈ Refl.normC G₀)
    (hz₂ : a₂ • ρ₀ + m₂ • y ∈ Refl.normC G₀) (hz₃ : a₃ • ρ₀ + m₃ • y ∈ Refl.normC G₀) :
    (1 + a₁) * m₂ = (1 + a₂) * m₁ ∧ (1 + a₁) * m₃ = (1 + a₃) * m₁ ∧
      (1 + a₂) * m₃ = (1 + a₃) * m₂ := by
  obtain ⟨w, hw, hwy, hwP⟩ := IPL.exists_w hirr hc0 hy hyr hys
  have hv : IPL.qC (spBil r s) (a, b) ≠ 0 := hq
  obtain ⟨g, hg⟩ : ∃ g : ℕ → Fin 4 → k, g = fun j => natAct (IPL.rotP r s ^ j)⁻¹ w := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : ℕ → k, V = fun j => spBil w r * ((IPL.rotC (spBil r s))^[j] (a, b)).1 +
      spBil w s * ((IPL.rotC (spBil r s))^[j] (a, b)).2 := ⟨_, rfl⟩
  have hgR : ∀ j, g j ∈ Refl.normC G₀ := fun j => by
    rw [hg]
    exact Refl.act_mem_normC hw (G₀.inv_mem (G₀.pow_mem (IPL.rotP_mem hr hs) j))
  have hval : ∀ j (a' m : k), spBil (g j) (a' • ρ₀ + m • y) = a' * V j + m * spBil w y := by
    intro j a' m
    rw [hg, hV, hρ₀P]
    exact IPL.bil_rotP_inv hyr hys w a b a' m j
  have hval₀ : ∀ j, spBil (g j) ρ₀ = V j := fun j => by
    simpa using hval j 1 0
  have h₀ : ∀ i j, i < 5 → j < 5 → spBil (g i) ρ₀ = 0 → spBil (g j) ρ₀ = 0 → i = j := by
    intro i j hi hj e₁ e₂
    rw [hval₀, hV] at e₁ e₂
    exact IPL.orbit_line_zero hc0 hc1 hv hwP i j hi hj e₁ e₂
  have hT : ∀ a' m : k, m ≠ 0 → ∀ i j l, i < 5 → j < 5 → l < 5 →
      spBil (g i) (a' • ρ₀ + m • y) = 0 → spBil (g j) (a' • ρ₀ + m • y) = 0 →
      spBil (g l) (a' • ρ₀ + m • y) = 0 → i = j ∨ i = l ∨ j = l := by
    intro a' m hm i j l hi hj hl e₁ e₂ e₃
    rw [hval] at e₁ e₂ e₃
    by_cases ha' : a' = 0
    · rw [ha', zero_mul, zero_add] at e₁
      exact absurd e₁ (mul_ne_zero hm hwy)
    · have e₁' := IPL.eq_div_of_add_eq_zero ha' e₁
      have e₂' := IPL.eq_div_of_add_eq_zero ha' e₂
      have e₃' := IPL.eq_div_of_add_eq_zero ha' e₃
      rw [hV] at e₁' e₂' e₃'
      exact IPL.orbit_line hc0 hc1 hv hwP _ i j l hi hj hl e₁' e₂' e₃'
  have d₀ : ∀ a' m : k, m ≠ 0 → ∀ j < 5, spBil (g j) ρ₀ = 0 →
      spBil (g j) (a' • ρ₀ + m • y) = 0 → False := by
    intro a' m hm j _ e₀ e
    rw [hval, ← hval₀, e₀, mul_zero, zero_add] at e
    exact mul_ne_zero hm hwy e
  have d : ∀ a' a'' m m' : k, m ≠ 0 → m ≠ m' → a' • ρ₀ + m • y ∈ Refl.normC G₀ →
      a'' • ρ₀ + m' • y ∈ Refl.normC G₀ → ∀ j < 5, spBil (g j) (a' • ρ₀ + m • y) = 0 →
      spBil (g j) (a'' • ρ₀ + m' • y) = 0 → False := by
    intro a' a'' m m' hm hmm' hz hz' j _ e e'
    rw [hval] at e e'
    have hX : V j ≠ 0 := fun hX0 => by
      rw [hX0, mul_zero, zero_add] at e
      exact mul_ne_zero hm hwy e
    have e3 : (a' * m' - a'' * m) * V j = 0 := by linear_combination m' * e - m * e'
    have e4 : a'' = a' * m' / m := by
      rw [eq_div_iff hm]
      linear_combination -(mul_eq_zero.mp e3).resolve_right hX
    have hsm : (m' / m) • (a' • ρ₀ + m • y) = a'' • ρ₀ + m' • y := by
      rw [e4]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    have h1 := Refl.eq_one_of_smul_mem hone hz (by rw [hsm]; exact hz')
    exact hmm' ((div_eq_one_iff_eq hm).mp h1).symm
  have good : ∀ a' a'' m m' : k, m ≠ 0 → a' • ρ₀ + m • y ∈ Refl.normC G₀ →
      a'' • ρ₀ + m' • y ∈ Refl.normC G₀ →
      (∃ j < 5, ¬spBil (g j) ρ₀ = 0 ∧ ¬spBil (g j) (a' • ρ₀ + m • y) = 0 ∧
        ¬spBil (g j) (a'' • ρ₀ + m' • y) = 0) → (1 + a') * m' = (1 + a'') * m := by
    rintro a' a'' m m' hm hz hz' ⟨j, -, e₀, e₁, e₂⟩
    exact IPL.ratio_of_w hS hone hc0 hρ₀P hρ₀ hy hyr hys (hgR j) hm hz hz' e₀ e₁ e₂
  rcases IPL.two_good_pairs h₀ (hT a₁ m₁ hm₁) (hT a₂ m₂ hm₂) (hT a₃ m₃ hm₃) (d₀ a₂ m₂ hm₂)
      (d₀ a₃ m₃ hm₃) (d a₁ a₂ m₁ m₂ hm₁ h₁₂ hz₁ hz₂) (d a₁ a₃ m₁ m₃ hm₁ h₁₃ hz₁ hz₃)
      (d a₂ a₃ m₂ m₃ hm₂ h₂₃ hz₂ hz₃) with ⟨g₁₂, g₁₃⟩ | ⟨g₁₂, g₂₃⟩ | ⟨g₁₃, g₂₃⟩
  · have e₁₂ := good a₁ a₂ m₁ m₂ hm₁ hz₁ hz₂ g₁₂
    have e₁₃ := good a₁ a₃ m₁ m₃ hm₁ hz₁ hz₃ g₁₃
    exact ⟨e₁₂, e₁₃, IPL.ratio_trans hm₁ e₁₂.symm e₁₃.symm⟩
  · have e₁₂ := good a₁ a₂ m₁ m₂ hm₁ hz₁ hz₂ g₁₂
    have e₂₃ := good a₂ a₃ m₂ m₃ hm₂ hz₂ hz₃ g₂₃
    exact ⟨e₁₂, IPL.ratio_trans hm₂ e₁₂ e₂₃.symm, e₂₃⟩
  · have e₁₃ := good a₁ a₃ m₁ m₃ hm₁ hz₁ hz₃ g₁₃
    have e₂₃ := good a₂ a₃ m₂ m₃ hm₂ hz₂ hz₃ g₂₃
    exact ⟨IPL.ratio_trans hm₃ e₁₃ e₂₃, e₁₃, e₂₃⟩

end CFSG.Quasithin.Ch3E213M.G41.Big
