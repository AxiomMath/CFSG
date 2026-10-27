module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PF3

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2]

omit [CharP k 2] in
theorem form_smul_add_perp (Q : QuadraticForm k (Fin 4 → k))
    (hQ : ∀ x y, QuadraticMap.polar Q x y = spBil x y) {r y : Fin 4 → k} (hyr : spBil y r = 0)
    (a : k) : Q (a • r + y) = a ^ 2 * Q r + Q y := by
  have h := hQ (a • r) y
  rw [QuadraticMap.polar, QuadraticMap.map_smul, smul_eq_mul, LinearMap.map_smul₂, bil_symm r y,
    hyr, smul_zero] at h
  linear_combination h

omit [CharP k 2] in
theorem eq_smul_add_prYL {r s x : Fin 4 → k} (hxr : spBil x r = 0) :
    x = (spBil x s / spBil r s) • r + prYL r s x := by
  conv_lhs => rw [eq_prPL_add r s x]
  rw [hxr, zero_div, zero_smul, add_zero]

theorem bil_eq_bil_prYL {r s x₁ x₂ : Fin 4 → k} (hc : spBil r s ≠ 0) (h₁ : spBil x₁ r = 0)
    (h₂ : spBil x₂ r = 0) : spBil x₁ x₂ = spBil (prYL r s x₁) (prYL r s x₂) := by
  have e1 := eq_smul_add_prYL (s := s) h₁
  have e2 := eq_smul_add_prYL (s := s) h₂
  have hy₂ := bil_prYL_left hc x₂
  have step1 : spBil x₁ x₂ = spBil x₁ (prYL r s x₂) := by
    conv_lhs => rw [e2]
    rw [map_add, map_smul, h₁, smul_zero, zero_add]
  have step2 : spBil x₁ (prYL r s x₂) = spBil (prYL r s x₁) (prYL r s x₂) := by
    conv_lhs => rw [e1]
    rw [LinearMap.map_add₂, LinearMap.map_smul₂, bil_symm r (prYL r s x₂), hy₂, smul_zero,
      zero_add]
  rw [step1, step2]

theorem mem_span_iff_prYL {r s x : Fin 4 → k} (hc : spBil r s ≠ 0) (hxr : spBil x r = 0) :
    x ∈ k ∙ r ↔ prYL r s x = 0 := by
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp h
    have h0 := prYL_smul_add hc a 0
    rwa [zero_smul, add_zero] at h0
  · intro h
    rw [eq_smul_add_prYL (s := s) hxr, h, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self r)

theorem eq_of_mem_span {G₀ : Subgroup (antiSp k)} (hone : Refl.OnePerCentre G₀) {r x : Fin 4 → k}
    (hr : r ∈ Refl.normC G₀) (hx : x ∈ Refl.normC G₀) (hxr : x ∈ k ∙ r) : x = r := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hxr
  rw [Refl.eq_one_of_smul_mem hone hr hx, one_smul]

theorem exists_linear_YO [Finite k]
    {n : ℕ} (hn : 2 ≤ n) (hk : Nat.card k = 2 ^ n) {G₀ : Subgroup (antiSp k)}
    (hone : Refl.OnePerCentre G₀)
    (hL4 : ∀ (G : Subgroup (antiSp k)) (F : Subfield k) (e e' : Fin 4 → k),
      Refl.OnePerCentre G → CaseB G F e e' →
      ∃ Q : QuadraticForm k (Fin 4 → k), (∀ x y, QuadraticMap.polar Q x y = spBil x y) ∧
        Q (eOne k) ≠ 0 ∧ ∀ z ∈ Refl.normC G, z 2 = 0 → proj z ≠ 0 → Q z = 1)
    {r s : Fin 4 → k} (hr : r ∈ Refl.normC G₀) (hs : s ∈ Refl.normC G₀) (hc : spBil r s ≠ 0)
    (hNoTwo : ∀ a b : k, a ^ 2 + b ^ 2 + spBil r s * a * b ≠ 0 → ∀ (π : Fin 4 → k) (l l' : k),
      π ∈ Refl.normC G₀ → spBil π r = 0 → spBil π s = 0 →
      a • r + b • s + l • π ∈ Refl.normC G₀ → a • r + b • s + l' • π ∈ Refl.normC G₀ → l = l')
    (hRatio : ∀ y : Fin 4 → k, spBil y r = 0 → spBil y s = 0 → ∀ t₀ μ ν : k,
      t₀ • y ∈ Refl.normC G₀ → μ • r + ν • y ∈ Refl.normC G₀ → ν = t₀ * (1 + μ))
    (hL4' : ∀ Q : QuadraticForm k (Fin 4 → k), (∀ x y, QuadraticMap.polar Q x y = spBil x y) →
      (∀ u ∈ Refl.normC G₀, spBil u r = 0 → u ∉ k ∙ r → Q u = 1) → ∀ F₁ : Subfield k,
      4 ≤ Nat.card F₁ → ∀ x₀ ∈ Refl.normC G₀, spBil x₀ r = 0 → x₀ ∉ k ∙ r →
      (∀ μ ∈ F₁, μ ≠ 0 → ∃ x' ∈ Refl.normC G₀, x' - μ • x₀ ∈ k ∙ r) → Q r = 1)
    (Q₀ : QuadraticForm k (Fin 4 → k)) (hQ₀ : ∀ x y, QuadraticMap.polar Q₀ x y = spBil x y)
    (hQ₀r : Q₀ r = 1) (hQ₀s : Q₀ s = 1) :
    ∃ ℓ : (Fin 4 → k) →ₗ[k] k,
      ∀ x ∈ Refl.normC G₀, spBil x r = 0 → Q₀ x + 1 = ℓ (prYL r s x) ^ 2 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hr0 : r ≠ 0 := hr.1
  have hkr : ∀ (ℓ : (Fin 4 → k) →ₗ[k] k) (x : Fin 4 → k), x ∈ Refl.normC G₀ → x ∈ k ∙ r →
      Q₀ x + 1 = ℓ (prYL r s x) ^ 2 := by
    intro ℓ x hx hxr
    rw [eq_of_mem_span hone hr hx hxr, hQ₀r]
    have h0 := prYL_smul_add hc 1 0
    rw [one_smul, zero_smul, add_zero] at h0
    rw [h0, map_zero]
    linear_combination h2
  have hK : ∀ x, spBil x r = 0 →
      Q₀ x = (spBil x s / spBil r s) ^ 2 + Q₀ (prYL r s x) := fun x hxr => by
    conv_lhs => rw [eq_smul_add_prYL (s := s) hxr]
    rw [form_smul_add_perp Q₀ hQ₀ (bil_prYL_left hc x), hQ₀r, mul_one]
  have hYne : ∀ x, spBil x r = 0 → x ∉ k ∙ r → prYL r s x ≠ 0 := fun x hxr hxn h =>
    hxn ((mem_span_iff_prYL hc hxr).mpr h)
  by_cases hx₀ : ∃ x₀ ∈ Refl.normC G₀, spBil x₀ r = 0 ∧ x₀ ∉ k ∙ r
  swap
  · refine ⟨0, fun x hx hxr => hkr 0 x hx ?_⟩
    by_contra hxn
    exact hx₀ ⟨x, hx, hxr, hxn⟩
  obtain ⟨x₀, hx₀, hx₀r, hx₀n⟩ := hx₀
  by_cases hnd : ∃ x₁ ∈ Refl.normC G₀, ∃ x₂ ∈ Refl.normC G₀, spBil x₁ r = 0 ∧ spBil x₂ r = 0 ∧
      spBil x₁ x₂ ≠ 0
  swap
  ·
    set y₀ := prYL r s x₀ with hy₀
    have hy₀0 : y₀ ≠ 0 := hYne x₀ hx₀r hx₀n
    obtain ⟨D, hD⟩ := homog_at hn hk hone hL4 hr hs hc hNoTwo hRatio Q₀ hQ₀ hQ₀r hQ₀s hy₀0
      (bil_prYL_left hc x₀) (bil_prYL_right hc x₀)
    obtain ⟨δ, hδ⟩ := Refl.exists_sq_eq D
    obtain ⟨w₀, hw₀⟩ := exists_bil_ne_zero hy₀0
    refine ⟨(δ / spBil w₀ y₀) • spBil w₀, fun x hx hxr => ?_⟩
    by_cases hxn : x ∈ k ∙ r
    · exact hkr _ x hx hxn
    have hperp : spBil (prYL r s x) y₀ = 0 := by
      rw [hy₀, ← bil_eq_bil_prYL hc hxr hx₀r]
      by_contra hne
      exact hnd ⟨x, hx, x₀, hx₀, hxr, hx₀r, hne⟩
    obtain ⟨α, β, l, hl⟩ := exists_eq_add_smul hc hy₀0 (bil_prYL_left hc x₀)
      (bil_prYL_right hc x₀) hperp
    have hxl : prYL r s x = l • y₀ := by
      have h1 := congrArg (prYL r s) hl
      rwa [prYL_of_perp (bil_prYL_left hc x) (bil_prYL_right hc x), map_add, prYL_smul_add hc,
        zero_add, map_smul, prYL_of_perp (bil_prYL_left hc x₀) (bil_prYL_right hc x₀)] at h1
    rw [hD x hx l hxl, hxl]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [div_mul_cancel₀ _ hw₀, ← hδ]
    ring
  obtain ⟨x₁, hx₁, x₂, hx₂, h₁, h₂, h12⟩ := hnd
  rcases split_at hn hk hone hL4 hr0 hx₁ hx₂ h₁ h₂ h12 with ⟨⟨QA, hQA, hQAr, hQA1⟩, hspan⟩ |
      ⟨⟨QB, hQB, -, hQB1⟩, ⟨F₁, hF₁, hcov⟩⟩
  ·
    have hfib : ∀ x ∈ Refl.normC G₀, ∀ x' ∈ Refl.normC G₀, spBil x r = 0 → x ∉ k ∙ r →
        x' - x ∈ k ∙ r → x' = x := by
      intro x hx x' hx' hxr hxn hdiff
      obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.mp hdiff
      have hx'e : x' = x + m • r := by rw [hm, add_sub_cancel]
      have hx'r : spBil x' r = 0 := by
        rw [hx'e, LinearMap.map_add₂, LinearMap.map_smul₂, bil_self, hxr, smul_zero, add_zero]
      have hY : prYL r s x' = prYL r s x := by
        have h0 := prYL_smul_add hc m 0
        rw [zero_smul, add_zero] at h0
        rw [hx'e, map_add, h0, add_zero]
      obtain ⟨D, hD⟩ := homog_at hn hk hone hL4 hr hs hc hNoTwo hRatio Q₀ hQ₀ hQ₀r hQ₀s
        (hYne x hxr hxn) (bil_prYL_left hc x) (bil_prYL_right hc x)
      have e1 := hD x hx 1 (one_smul _ _).symm
      have e2 := hD x' hx' 1 (by rw [hY, one_smul])
      rw [hK x hxr] at e1
      rw [hK x' hx'r, hY] at e2
      have hsq : (spBil x' s / spBil r s - spBil x s / spBil r s) ^ 2 = 0 := by
        linear_combination e2 - e1 + (spBil x s / spBil r s) ^ 2 * h2 -
          (spBil x' s / spBil r s * (spBil x s / spBil r s)) * h2
      have ha : spBil x' s / spBil r s = spBil x s / spBil r s :=
        sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)
      rw [eq_smul_add_prYL (s := s) hx'r, ha, hY, ← eq_smul_add_prYL (s := s) hxr]
    obtain ⟨ℓ', hℓ'⟩ := exists_linear_sq (Q₀ + QA) (fun x y => by
      rw [FunLike.coe_add, QuadraticMap.polar_add, hQ₀, hQA]
      linear_combination spBil x y * h2)
    set d := spBil (prYL r s x₁) (prYL r s x₂) with hd
    have hd0 : d ≠ 0 := by rw [hd, ← bil_eq_bil_prYL hc h₁ h₂]; exact h12
    set m : (Fin 4 → k) →ₗ[k] k := (d⁻¹ * (spBil x₁ s / spBil r s)) • spBil (prYL r s x₂) +
      (d⁻¹ * (spBil x₂ s / spBil r s)) • spBil (prYL r s x₁) with hm
    have hm1 : m (prYL r s x₁) = spBil x₁ s / spBil r s := by
      simp only [hm, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, bil_self, mul_zero,
        add_zero]
      rw [bil_symm (prYL r s x₂), ← hd]
      field_simp
    have hm2 : m (prYL r s x₂) = spBil x₂ s / spBil r s := by
      simp only [hm, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, bil_self, mul_zero,
        zero_add]
      rw [← hd]
      field_simp
    clear_value m
    refine ⟨m + ℓ', fun x hx hxr => ?_⟩
    by_cases hxn : x ∈ k ∙ r
    · exact hkr _ x hx hxn
    obtain ⟨α, β, hαβ⟩ := hspan hfib x hx hxr hxn
    have hQAx : QA (prYL r s x) = 1 := by
      have h1 := hQA1 x hx hxr hxn
      conv_lhs at h1 => rw [eq_smul_add_prYL (s := s) hxr]
      rwa [form_smul_add_perp QA hQA (bil_prYL_left hc x), hQAr, mul_zero, zero_add] at h1
    have hcoef : spBil x s / spBil r s = m (prYL r s x) := by
      have hprY : prYL r s x = α • prYL r s x₁ + β • prYL r s x₂ := by
        rw [hαβ, map_add, map_smul, map_smul]
      have hxs : spBil x s = α * spBil x₁ s + β * spBil x₂ s := by
        rw [hαβ, LinearMap.map_add₂, LinearMap.map_smul₂, LinearMap.map_smul₂, smul_eq_mul,
          smul_eq_mul]
      rw [hprY, map_add, map_smul, map_smul, hm1, hm2, hxs, smul_eq_mul, smul_eq_mul]
      ring
    rw [hK x hxr, hcoef, LinearMap.add_apply]
    have e := hℓ' (prYL r s x)
    rw [add_apply, hQAx] at e
    linear_combination e - (m (prYL r s x) * ℓ' (prYL r s x)) * h2
  ·
    have hQBr : QB r = 1 := hL4' QB hQB hQB1 F₁ hF₁ x₁ hx₁ h₁
      (fun h => h12 (by
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp h
        rw [LinearMap.map_smul₂, bil_symm r x₂, h₂, smul_zero]))
      (fun μ hμ hμ0 => hcov x₁ hx₁ h₁ (fun h => h12 (by
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp h
        rw [LinearMap.map_smul₂, bil_symm r x₂, h₂, smul_zero])) μ hμ hμ0)
    obtain ⟨ℓ, hℓ⟩ := exists_linear_sq (Q₀ + QB) (fun x y => by
      rw [FunLike.coe_add, QuadraticMap.polar_add, hQ₀, hQB]
      linear_combination spBil x y * h2)
    refine ⟨ℓ, fun x hx hxr => ?_⟩
    by_cases hxn : x ∈ k ∙ r
    · exact hkr _ x hx hxn
    have hQBx := hQB1 x hx hxr hxn
    conv_lhs at hQBx => rw [eq_smul_add_prYL (s := s) hxr]
    rw [form_smul_add_perp QB hQB (bil_prYL_left hc x), hQBr, mul_one] at hQBx
    have e := hℓ (prYL r s x)
    rw [add_apply] at e
    rw [hK x hxr]
    linear_combination e + hQBx + (1 - QB (prYL r s x)) * h2

end CFSG.Quasithin.Ch3E213M.G41.Big
