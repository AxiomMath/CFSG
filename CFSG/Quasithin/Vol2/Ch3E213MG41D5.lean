module

public import CFSG.Quasithin.Vol2.Ch3E213MG41D4
public import CFSG.Quasithin.Vol2.Ch3E213MG41D2

public section

namespace CFSG.Quasithin.Ch3E213M.G41

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2]

variable {G₀ : Subgroup (antiSp k)} {F₀ : Subfield k}

variable [Finite k] {n : ℕ}

theorem exists_frame (hk : Nat.card k = 2 ^ n) (hF4 : 4 ≤ Nat.card F₀)
    (hirr : IsIrreducibleSp4 G₀) (hD : (transvSet G₀).Nonempty)
    (hG : ∀ W, DInv G₀ W → W = ⊥ ∨ W = ⊤) {x₁ y₁ : Fin 4 → k} (hx₁ : IsNorm G₀ F₀ x₁)
    (hy₁ : IsNorm G₀ F₀ y₁) (hxy : spBil x₁ y₁ = 1) :
    ∃ x₂ y₂ : Fin 4 → k, IsNorm G₀ F₀ x₂ ∧ IsNorm G₀ F₀ y₂ ∧ IsNorm G₀ F₀ (x₁ + x₂) ∧
      spBil x₂ y₂ = 1 ∧ spBil x₂ x₁ = 0 ∧ spBil x₂ y₁ = 0 ∧ spBil y₂ x₁ = 0 ∧
      spBil y₂ y₁ = 0 := by
  obtain ⟨m, hm, hm0, hm₂⟩ := exists_mixing hk hF4 hG (y := y₁) hx₁
  obtain ⟨hm₂x, hm₂y⟩ := perpPart_perp hxy m
  have hhub := isNorm_hub_of_mix hk hF4 hx₁ hy₁ hxy hm hm0
  set m₂ := perpPart x₁ y₁ m with hm₂def
  have hxm₂ : spBil x₁ m₂ = 0 := by rw [bil_symm]; exact hm₂x
  have hym₂ : spBil y₁ m₂ = 0 := by rw [bil_symm]; exact hm₂y
  obtain ⟨s, hs, hms⟩ : ∃ s, IsNorm G₀ F₀ s ∧ spBil m₂ s ≠ 0 := by
    obtain ⟨y, hy, hmy⟩ : ∃ y ∈ centres G₀, spBil m₂ y ≠ 0 := by
      by_contra h
      simp only [not_exists, not_and, not_not] at h
      exact hm₂ (eq_zero_of_orth_span (span_centres_eq_top hirr hD) h)
    obtain ⟨μ, hμ, hμy⟩ := exists_isNorm_smul hk hF4 hG hx₁ hy
    refine ⟨μ • y, hμy, ?_⟩
    rw [LinearMap.map_smul, smul_eq_mul]
    exact mul_ne_zero hμ hmy
  obtain ⟨hs₂x, hs₂y⟩ := perpPart_perp hxy s
  have hms₂ : spBil m₂ (perpPart x₁ y₁ s) = spBil m₂ s := by
    conv_rhs => rw [eq_perpPart x₁ y₁ s]
    simp [hm₂x, hm₂y]
  set s₂ := perpPart x₁ y₁ s with hs₂def
  obtain ⟨hnm₂, hns₂⟩ : IsNorm G₀ F₀ m₂ ∧ IsNorm G₀ F₀ s₂ := by
    by_cases hs0 : spBil s y₁ ≠ 0 ∨ spBil s x₁ ≠ 0
    · have hhub' := isNorm_hub_of_mix hk hF4 hx₁ hy₁ hxy hs hs0
      have h1 : spBil m₂ s₂ ≠ 0 := by rw [hms₂]; exact hms
      have h2 : spBil s₂ m₂ ≠ 0 := by rwa [bil_symm]
      exact ⟨isNorm_of_hub hk hF4 hx₁ hy₁ hxy hm₂x hm₂y hhub hs₂x hs₂y hhub' h1,
        isNorm_of_hub hk hF4 hx₁ hy₁ hxy hs₂x hs₂y hhub' hm₂x hm₂y hhub h2⟩
    · simp only [not_or, not_not] at hs0
      have hss : s₂ = s := by
        rw [hs₂def, perpPart, hs0.1, hs0.2, zero_smul, zero_smul, sub_zero, sub_zero]
      have hsx : spBil s x₁ = 0 := hs0.2
      have hsy : spBil s y₁ = 0 := hs0.1
      have hhub' := isNorm_hub_of_perp hk hF4 hx₁ hy₁ hxy hm₂x hm₂y hhub hsx hsy hs hms
      refine ⟨isNorm_of_hub hk hF4 hx₁ hy₁ hxy hm₂x hm₂y hhub hsx hsy hhub' hms, ?_⟩
      rw [hss]
      exact hs
  have hδ : spBil m₂ s₂ ≠ 0 := by rw [hms₂]; exact hms
  have hδF : (spBil m₂ s₂)⁻¹ ∈ F₀ := F₀.inv_mem (bil_mem_of_isNorm hk hF4 hnm₂ hns₂)
  refine ⟨m₂, (spBil m₂ s₂)⁻¹ • s₂, hnm₂, isNorm_smul hns₂ hδF (inv_ne_zero hδ), hhub, ?_,
    hm₂x, hm₂y, ?_, ?_⟩
  · rw [LinearMap.map_smul, smul_eq_mul, inv_mul_cancel₀ hδ]
  · rw [LinearMap.BilinForm.smul_left, hs₂x, mul_zero]
  · rw [LinearMap.BilinForm.smul_left, hs₂y, mul_zero]

theorem spW_of_frame (hk : Nat.card k = 2 ^ n) (hF4 : 4 ≤ Nat.card F₀) {x₁ y₁ x₂ y₂ : Fin 4 → k}
    (hx₁ : IsNorm G₀ F₀ x₁) (hy₁ : IsNorm G₀ F₀ y₁) (hxy : spBil x₁ y₁ = 1)
    (hx₂ : IsNorm G₀ F₀ x₂) (hy₂ : IsNorm G₀ F₀ y₂) (hmix : IsNorm G₀ F₀ (x₁ + x₂))
    (hxy₂ : spBil x₂ y₂ = 1) (h21 : spBil x₂ x₁ = 0) (h22 : spBil x₂ y₁ = 0)
    (h23 : spBil y₂ x₁ = 0) (h24 : spBil y₂ y₁ = 0) : G41SpW G₀ := by
  have hyx : spBil y₁ x₁ = 1 := by rw [bil_symm, hxy]
  have hyx₂ : spBil y₂ x₂ = 1 := by rw [bil_symm, hxy₂]
  have h21' : spBil x₁ x₂ = 0 := by rw [bil_symm, h21]
  have h22' : spBil y₁ x₂ = 0 := by rw [bil_symm, h22]
  have h23' : spBil x₁ y₂ = 0 := by rw [bil_symm, h23]
  have h24' : spBil y₁ y₂ = 0 := by rw [bil_symm, h24]
  set e : Fin 4 → Fin 4 → k := ![x₁, x₂, y₂, y₁] with hedef
  have he : ∀ s t, spBil (e s) (e t) = minorJ k s t := by
    intro s t
    fin_cases s <;> fin_cases t <;>
      simp [hedef, minorJ_apply, bil_self, hxy, hyx, hxy₂, hyx₂, h21, h22, h23, h24, h21',
        h22', h23', h24']
  refine spW_of_basis hk hF4 e he ?_
  intro c hc hc0
  have hsum : ∑ j, c j • e j = c 0 • x₁ + c 3 • y₁ + (c 1 • x₂ + c 2 • y₂) := by
    rw [Fin.sum_univ_four]
    show c 0 • x₁ + c 1 • x₂ + c 2 • y₂ + c 3 • y₁ = _
    abel
  rw [hsum]
  have hnz : (c 0 ≠ 0 ∨ c 3 ≠ 0) ∨ (c 1 ≠ 0 ∨ c 2 ≠ 0) := by
    by_contra h
    simp only [not_or, not_not] at h
    apply hc0
    funext j
    fin_cases j
    exacts [h.1.1, h.2.1, h.2.2, h.1.2]
  have hu0x : spBil (0 : Fin 4 → k) x₁ = 0 := by simp
  have hu0y : spBil (0 : Fin 4 → k) y₁ = 0 := by simp
  by_cases h12 : c 1 ≠ 0 ∨ c 2 ≠ 0
  · by_cases h03 : c 0 ≠ 0 ∨ c 3 ≠ 0
    ·
      have s1 := isNorm_hub hx₁ hy₁ hxy h21 h22 hmix (hc 0) (hc 3) h03
      have hux : spBil (c 0 • x₁ + c 3 • y₁) x₂ = 0 := by simp [h21', h22']
      have huy : spBil (c 0 • x₁ + c 3 • y₁) y₂ = 0 := by simp [h23', h24']
      have s2 := isNorm_hub hx₂ hy₂ hxy₂ hux huy (by rwa [add_comm] at s1) (hc 1) (hc 2) h12
      convert s2 using 1
      abel
    · simp only [not_or, not_not] at h03
      have hux : spBil (0 : Fin 4 → k) x₂ = 0 := by simp
      have huy : spBil (0 : Fin 4 → k) y₂ = 0 := by simp
      have s2 := isNorm_hub hx₂ hy₂ hxy₂ hux huy (by simpa using hx₂) (hc 1) (hc 2) h12
      convert s2 using 1
      rw [h03.1, h03.2]
      simp
  · have h03 := hnz.resolve_right h12
    simp only [not_or, not_not] at h12
    have s1 := isNorm_hub hx₁ hy₁ hxy hu0x hu0y (by simpa using hx₁) (hc 0) (hc 3) h03
    convert s1 using 1
    rw [h12.1, h12.2]
    simp

theorem spW_of_large (hk : Nat.card k = 2 ^ n) (hirr : IsIrreducibleSp4 G₀)
    (hD : (transvSet G₀).Nonempty) (hG : ∀ W, DInv G₀ W → W = ⊥ ∨ W = ⊤) {x₀ : Fin 4 → k}
    (hx₀ : x₀ ∈ centres G₀) (h4 : 4 ≤ Nat.card (Lam G₀ x₀)) : G41SpW G₀ := by
  obtain ⟨F₁, x₁, y₁, hF4, hx₁, hy₁, hxy⟩ := exists_init_pair hk hirr hD hx₀ h4
  obtain ⟨x₂, y₂, hx₂, hy₂, hmix, hxy₂, h21, h22, h23, h24⟩ :=
    exists_frame hk hF4 hirr hD hG hx₁ hy₁ hxy
  exact spW_of_frame hk hF4 hx₁ hy₁ hxy hx₂ hy₂ hmix hxy₂ h21 h22 h23 h24

end CFSG.Quasithin.Ch3E213M.G41
