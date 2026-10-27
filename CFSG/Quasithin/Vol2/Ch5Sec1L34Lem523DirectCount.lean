module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectSemi

public section

namespace CFSG.Quasithin.H13.Direct523Count

open CFSG.Quasithin.H13.Direct523Semi

variable {K : Type} [Field K]

theorem sigma_eq_refl_of_id {A : (Fin 2 → K) ≃+ (Fin 2 → K)} {σA : K ≃+* K} (hσA : IsSemi A σA)
    (hA : A = AddEquiv.refl _) : σA = RingEquiv.refl K := by
  apply RingEquiv.ext
  intro a
  have h := hσA.smul a e₁
  rw [hA] at h
  have h0 := congrFun h 0
  simpa [e₁] using h0.symm

theorem uB_commute_iff [Finite K] {a₀ : K} (ha₀ : a₀ ≠ 0)
    {A : (Fin 2 → K) ≃+ (Fin 2 → K)} {σA : K ≃+* K} (hσA : IsSemi A σA)
    (hσA2 : ∀ x, σA x = x ^ 2) (hfixA : A (a₀ • e₁) = a₀ • e₁) (hb : A e₂ 1 ≠ 0) (β : K)
    (hcomm : (uB β).trans A = A.trans (uB β)) :
    β = 0 ∨ β = A e₂ 1 / (a₀ * (σA a₀)⁻¹) := by
  have hAe1 : A e₁ = (a₀ * (σA a₀)⁻¹) • e₁ := semi_e₁ hσA ha₀ hfixA
  have hσa0 : σA a₀ ≠ 0 := by
    intro h
    exact ha₀ ((map_eq_zero_iff σA σA.injective).1 h)
  have hc0 : a₀ * (σA a₀)⁻¹ ≠ 0 := mul_ne_zero ha₀ (inv_ne_zero hσa0)
  set c0 : K := a₀ * (σA a₀)⁻¹ with hc0def
  set b : K := A e₂ 1 with hbdef
  have h2 := congrArg (fun F : (Fin 2 → K) ≃+ (Fin 2 → K) => F e₂) hcomm
  simp only [AddEquiv.trans_apply] at h2
  rw [uB_e₂, map_add, hσA.smul β e₁, hAe1, hσA2 β] at h2
  have h0 := congrFun h2 0
  simp [uB_apply, e₁, smul_eq_mul] at h0
  rw [← hbdef] at h0
  have hprod : β * (β * c0 - b) = 0 := by linear_combination h0
  rcases mul_eq_zero.1 hprod with h | h
  · exact Or.inl h
  · right
    rw [eq_div_iff hc0]
    linear_combination h

theorem count_le_four [Finite K] (hK : Nat.card K = 4) [CharP K 2] {a₀ : K} (ha₀ : a₀ ≠ 0)
    (𝓢 : Set ((Fin 2 → K) ≃+ (Fin 2 → K)))
    (hfix : ∀ B ∈ 𝓢, B (a₀ • e₁) = a₀ • e₁)
    (hinv : ∀ B ∈ 𝓢, ∀ w, B (B w) = w)
    (hsemi : ∀ B ∈ 𝓢, ∃ σ : K ≃+* K, IsSemi B σ)
    (hcomp : ∀ B ∈ 𝓢, ∀ C ∈ 𝓢, B.trans C ∈ 𝓢)
    (hcomm : ∀ B ∈ 𝓢, ∀ C ∈ 𝓢, B.trans C = C.trans B)
    {A : (Fin 2 → K) ≃+ (Fin 2 → K)} (hA : A ∈ 𝓢) {σA : K ≃+* K} (hσA : IsSemi A σA)
    (hσA2 : ∀ x, σA x = x ^ 2) :
    ∃ c : K, c ≠ 0 ∧ (∀ β : K, (uB β).trans A = A.trans (uB β) → β = 0 ∨ β = c) ∧
      ∀ B ∈ 𝓢, B = uB 0 ∨ B = uB c ∨ B = A.trans (uB 0) ∨ B = A.trans (uB c) := by
  have h4 : ∀ x : K, x ^ 4 = x := fun x => by
    have := Direct523Gal.pow_natCard x
    rwa [hK] at this
  have hAe1 : A e₁ = (a₀ * (σA a₀)⁻¹) • e₁ := semi_e₁ hσA ha₀ (hfix A hA)
  have hσa0 : σA a₀ ≠ 0 := by
    intro h
    exact ha₀ ((map_eq_zero_iff σA σA.injective).1 h)
  have hc0 : a₀ * (σA a₀)⁻¹ ≠ 0 := mul_ne_zero ha₀ (inv_ne_zero hσa0)
  set c0 : K := a₀ * (σA a₀)⁻¹ with hc0def
  have hb : A e₂ 1 ≠ 0 := by
    intro hb0
    have hx : ∀ x : Fin 2 → K, A x 1 = 0 := by
      intro x
      have he1 : (A e₁) 1 = 0 := by rw [hAe1]; simp [e₁]
      rw [IsSemi.apply hσA x]
      simp [he1, hb0]
    have := hx (A.symm e₂)
    rw [A.apply_symm_apply] at this
    simp [e₂] at this
  set b : K := A e₂ 1 with hbdef
  set c : K := b / c0 with hcdef
  have hbc : A e₂ 1 / (a₀ * (σA a₀)⁻¹) ≠ 0 := div_ne_zero hb hc0
  have hlin : ∀ β : K, uB β ∈ 𝓢 → β = 0 ∨ β = A e₂ 1 / (a₀ * (σA a₀)⁻¹) := fun β hβ =>
    uB_commute_iff ha₀ hσA hσA2 (hfix A hA) hb β (hcomm (uB β) hβ A hA)
  set c : K := A e₂ 1 / (a₀ * (σA a₀)⁻¹) with hcdef
  have hlin' : ∀ β : K, (uB β).trans A = A.trans (uB β) → β = 0 ∨ β = c := fun β hβ =>
    uB_commute_iff ha₀ hσA hσA2 (hfix A hA) hb β hβ
  refine ⟨c, hbc, fun β hβ => hlin' β hβ, fun B hB => ?_⟩
  obtain ⟨σB, hσB⟩ := hsemi B hB
  rcases semi_aut_cases hK σB with hid | hfr
  ·
    subst hid
    obtain ⟨β, rfl⟩ := linear_eq_uB ha₀ hσB (hfix B hB) (hinv B hB)
    rcases hlin β hB with h | h
    · left; rw [h]
    · right; left; rw [h]
  ·
    have hAB : A.trans B ∈ 𝓢 := hcomp A hA B hB
    have hsemiAB : IsSemi (A.trans B) (σA.trans σB) := by
      unfold IsSemi
      intro a w
      show B (A (a • w)) = (σA.trans σB) a • B (A w)
      rw [hσA.smul a w, hσB.smul, RingEquiv.trans_apply]
    have hid : σA.trans σB = RingEquiv.refl K := by
      apply RingEquiv.ext
      intro x
      rw [RingEquiv.trans_apply, hσA2, hfr, RingEquiv.refl_apply]
      calc (x ^ 2) ^ 2 = x ^ 4 := by ring
        _ = x := h4 x
    rw [hid] at hsemiAB
    have hfixAB : (A.trans B) (a₀ • e₁) = a₀ • e₁ := by
      show B (A (a₀ • e₁)) = a₀ • e₁
      rw [hfix A hA, hfix B hB]
    obtain ⟨β, hβ⟩ := linear_eq_uB ha₀ hsemiAB hfixAB (hinv (A.trans B) hAB)
    have hBeq : B = A.trans (uB β) := by
      rw [← hβ]
      refine AddEquiv.ext fun x => ?_
      simp only [AddEquiv.trans_apply]
      rw [hinv A hA]
    rw [hBeq]
    rw [hβ] at hAB
    rcases hlin β hAB with h | h
    · right; right; left; rw [h]
    · right; right; right; rw [h]

end CFSG.Quasithin.H13.Direct523Count
