module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PE7

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp)

variable {k : Type} [Field k] [CharP k 2] {G₀ : Subgroup (antiSp k)}

theorem eq_one_of_three_lifts [Finite k] (hS : SectionSplit G₀) (hone : Refl.OnePerCentre G₀)
    (hirr : IsIrreducibleSp4 (Subgroup.closure (transvSet G₀))) {r s : Fin 4 → k}
    (hr : r ∈ Refl.normC G₀) (hs : s ∈ Refl.normC G₀) (hc0 : spBil r s ≠ 0)
    (hc1 : spBil r s ≠ 1) {a b : k} (hq : a ^ 2 + b ^ 2 + spBil r s * a * b ≠ 0)
    {ρ₀ : Fin 4 → k} (hρ₀P : ρ₀ = a • r + b • s) (hρ₀ : ρ₀ ∈ Refl.normC G₀)
    {Q : (Fin 4 → k) → k}
    (hQadd : ∀ u v, spBil u ρ₀ = 0 → spBil v ρ₀ = 0 → Q (u + v) = Q u + Q v + spBil u v)
    (hQsmul : ∀ (c : k) u, spBil u ρ₀ = 0 → Q (c • u) = c ^ 2 * Q u)
    (hQ1 : ∀ u ∈ Refl.normC G₀, spBil u ρ₀ = 0 → u ∉ k ∙ ρ₀ → Q u = 1) {y : Fin 4 → k}
    (hy : y ≠ 0) (hyr : spBil y r = 0) (hys : spBil y s = 0) {a₁ a₂ a₃ m₁ m₂ m₃ : k}
    (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) (hm₃ : m₃ ≠ 0) (h₁₂ : m₁ ≠ m₂) (h₁₃ : m₁ ≠ m₃)
    (h₂₃ : m₂ ≠ m₃) (hz₁ : a₁ • ρ₀ + m₁ • y ∈ Refl.normC G₀)
    (hz₂ : a₂ • ρ₀ + m₂ • y ∈ Refl.normC G₀) (hz₃ : a₃ • ρ₀ + m₃ • y ∈ Refl.normC G₀) :
    Q ρ₀ = 1 := by
  have h0 : (2 : k) = 0 := CharTwo.two_eq_zero
  obtain ⟨e₁₂, -, -⟩ := ratio_eq_of_three hS hone hirr hr hs hc0 hc1 hq hρ₀P hρ₀ hy hyr hys
    hm₁ hm₂ hm₃ h₁₂ h₁₃ h₂₃ hz₁ hz₂ hz₃
  have hρρ : spBil ρ₀ ρ₀ = 0 := bil_self ρ₀
  have hρy : spBil ρ₀ y = 0 := by rw [hρ₀P]; exact IPL.bil_coord_perp hyr hys a b
  have hyρ : spBil y ρ₀ = 0 := by rw [bil_symm]; exact hρy
  have hQz : ∀ a' m : k, m ≠ 0 → a' • ρ₀ + m • y ∈ Refl.normC G₀ →
      a' ^ 2 * Q ρ₀ + m ^ 2 * Q y = 1 := by
    intro a' m hm hz
    have h1 : spBil (a' • ρ₀) ρ₀ = 0 := by simp [map_smul, hρρ]
    have h2 : spBil (m • y) ρ₀ = 0 := by simp [map_smul, hyρ]
    have := hQ1 _ hz (by rw [map_add, LinearMap.add_apply, h1, h2, add_zero])
      (IPL.add_smul_not_mem hc0 hρ₀P hy hyr hys a' hm)
    rw [hQadd _ _ h1 h2, hQsmul _ _ hρρ, hQsmul _ _ hyρ] at this
    simpa [map_smul, hρy] using this
  obtain ⟨t, ht⟩ := Refl.exists_sq_eq (Q ρ₀)
  obtain ⟨σ, hσ⟩ := Refl.exists_sq_eq (Q y)
  have hlin : ∀ a' m : k, m ≠ 0 → a' • ρ₀ + m • y ∈ Refl.normC G₀ → a' * t + m * σ = 1 := by
    intro a' m hm hz
    apply eq_one_of_sq_eq_one
    have := hQz a' m hm hz
    rw [← ht, ← hσ] at this
    linear_combination this + (a' * t * m * σ) * h0
  have l₁ := hlin a₁ m₁ hm₁ hz₁
  have l₂ := hlin a₂ m₂ hm₂ hz₂
  have key : (t + 1) * (m₂ - m₁) = 0 := by linear_combination t * e₁₂ - m₂ * l₁ + m₁ * l₂
  have ht1 : t + 1 = 0 := (mul_eq_zero.mp key).resolve_right (sub_ne_zero.mpr h₁₂.symm)
  rw [← ht]
  linear_combination (t - 1) * ht1

theorem quad_eq_one_at [Finite k] (hS : SectionSplit G₀) (hone : Refl.OnePerCentre G₀)
    (hirr : IsIrreducibleSp4 (Subgroup.closure (transvSet G₀))) {r s : Fin 4 → k}
    (hr : r ∈ Refl.normC G₀) (hs : s ∈ Refl.normC G₀) (hc0 : spBil r s ≠ 0)
    (hc1 : spBil r s ≠ 1) {a b : k} (hq : a ^ 2 + b ^ 2 + spBil r s * a * b ≠ 0)
    {ρ₀ : Fin 4 → k} (hρ₀P : ρ₀ = a • r + b • s) (hρ₀ : ρ₀ ∈ Refl.normC G₀)
    (Q : QuadraticForm k (Fin 4 → k)) (hpol : ∀ x y, QuadraticMap.polar Q x y = spBil x y)
    (hQ1 : ∀ u ∈ Refl.normC G₀, spBil u ρ₀ = 0 → u ∉ k ∙ ρ₀ → Q u = 1) {F₁ : Subfield k}
    (hF₁ : 4 ≤ Nat.card F₁) {x₀ : Fin 4 → k} (hx₀ρ : spBil x₀ ρ₀ = 0) (hx₀' : x₀ ∉ k ∙ ρ₀)
    (hcov : ∀ μ ∈ F₁, μ ≠ 0 → ∃ x' ∈ Refl.normC G₀, x' - μ • x₀ ∈ k ∙ ρ₀) : Q ρ₀ = 1 := by
  have h0 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hsr : spBil s r = spBil r s := bil_symm s r
  have horth : a * spBil x₀ r + b * spBil x₀ s = 0 := by
    rw [hρ₀P] at hx₀ρ
    simpa [map_add, map_smul] using hx₀ρ
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : k, a₀ * ((a ^ 2 + b ^ 2 + spBil r s * a * b) * spBil r s) =
      a * spBil x₀ s + b * spBil x₀ r + spBil r s * a * spBil x₀ r :=
    ⟨_, div_mul_cancel₀ _ (mul_ne_zero hq hc0)⟩
  have hρr : spBil ρ₀ r = b * spBil r s := by
    rw [hρ₀P]
    simp [map_add, map_smul, bil_self, hsr]
  have hρs : spBil ρ₀ s = a * spBil r s := by
    rw [hρ₀P]
    simp [map_add, map_smul, bil_self]
  have hyr : spBil (x₀ - a₀ • ρ₀) r = 0 := by
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hρr, smul_eq_mul]
    refine mul_left_cancel₀ hq ?_
    linear_combination (-b) * ha₀ + a * horth + (-a * b * spBil x₀ s) * h0
  have hys : spBil (x₀ - a₀ • ρ₀) s = 0 := by
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hρs, smul_eq_mul]
    refine mul_left_cancel₀ hq ?_
    linear_combination (-a) * ha₀ + (b + spBil r s * a) * horth +
      (-a * (b + spBil r s * a) * spBil x₀ r) * h0
  have hy0 : x₀ - a₀ • ρ₀ ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact hx₀' (h ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self ρ₀))
  obtain ⟨μ₀, hμ₀F, hμ₀0, hμ₀1⟩ := exists_mem_ne_ne (F₀ := F₁) (by omega) (0 : k) 1
  have hμ₁ : μ₀ + 1 ≠ 0 := fun h => hμ₀1 (by linear_combination h - h0)
  have lift : ∀ μ ∈ F₁, μ ≠ 0 → ∃ a' : k, a' • ρ₀ + μ • (x₀ - a₀ • ρ₀) ∈ Refl.normC G₀ := by
    intro μ hμF hμ0
    obtain ⟨x', hx', hmem⟩ := hcov μ hμF hμ0
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
    refine ⟨μ * a₀ + t, ?_⟩
    have e : (μ * a₀ + t) • ρ₀ + μ • (x₀ - a₀ • ρ₀) = x' := by
      rw [add_smul, smul_sub, smul_smul, ht]
      abel
    rw [e]
    exact hx'
  obtain ⟨a₁, h₁⟩ := lift 1 F₁.one_mem one_ne_zero
  obtain ⟨a₂, h₂⟩ := lift μ₀ hμ₀F hμ₀0
  obtain ⟨a₃, h₃⟩ := lift (μ₀ + 1) (F₁.add_mem hμ₀F F₁.one_mem) hμ₁
  refine eq_one_of_three_lifts hS hone hirr hr hs hc0 hc1 hq hρ₀P hρ₀ (Q := Q)
    (fun u v _ _ => ?_) (fun c u _ => ?_) hQ1 hy0 hyr hys one_ne_zero hμ₀0 hμ₁
    (Ne.symm hμ₀1) (fun h => hμ₀0 (by linear_combination -h))
    (fun h => one_ne_zero (by linear_combination -h)) h₁ h₂ h₃
  · have := hpol u v
    unfold QuadraticMap.polar at this
    linear_combination this
  · rw [QuadraticMap.map_smul, smul_eq_mul, sq]

end CFSG.Quasithin.Ch3E213M.G41.Big
