module

public import CFSG.SignalizerFunctorTheorem.NonLocal.Weights

public section

open Module Module.End
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocal

variable {F W G : Type*} [Field F] [AddCommGroup W] [Module F W] [Group G]

theorem card_le_finrank_of_translations [IsAlgClosed F] [FiniteDimensional F W]
    (ρ : G →* End F W) (A Z : Subgroup G) (hA : IsMulCommutative A) [Finite A]
    (hinv : (Nat.card A : F) ≠ 0) (hZA : Z ≤ A)
    {ι : Type*} [Finite ι] (y : ι → G)
    (hcomm : ∀ i, ∀ a ∈ A, ⁅(y i)⁻¹, a⁆ ∈ Z)
    (hnt : ∃ z ∈ Z, ρ z ≠ 1)
    (hdist : ∀ ξ : G → F, (∀ z ∈ Z, ∀ z' ∈ Z, ξ (z * z') = ξ z * ξ z') → (∀ z ∈ Z, ξ z ≠ 0) →
      (∃ z ∈ Z, ξ z ≠ 1) → (∃ w : W, w ≠ 0 ∧ ∀ z ∈ Z, ρ z w = ξ z • w) →
      ∀ i j, i ≠ j → ∃ a ∈ A, ξ ⁅(y i)⁻¹, a⁆ ≠ ξ ⁅(y j)⁻¹, a⁆) :
    Nat.card ι ≤ finrank F W := by
  classical
  obtain ⟨z₀, hz₀Z, hz₀⟩ := hnt
  have hT : ρ z₀ - 1 ≠ 0 := sub_ne_zero.mpr hz₀
  obtain ⟨χ, w₀, hev0, hTw⟩ := exists_jointEigenvector_apply_ne_zero ρ A hA hinv (ρ z₀ - 1) hT
  have hw0 : w₀ ≠ 0 := by
    rintro rfl
    exact hTw (map_zero _)
  have hχz₀ : χ ⟨z₀, hZA hz₀Z⟩ ≠ 1 := by
    intro h
    apply hTw
    rw [LinearMap.sub_apply, hev0 ⟨z₀, hZA hz₀Z⟩, h, one_smul, Module.End.one_apply, sub_self]
  have hχmul : ∀ a b : A, χ (a * b) = χ a * χ b := by
    intro a b
    have h1 : ρ ((a * b : A) : G) w₀ = (χ a * χ b) • w₀ := by
      rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hev0 b, map_smul, hev0 a, smul_smul,
        mul_comm]
    have h2 := hev0 (a * b)
    rw [h1] at h2
    exact (smul_left_injective F hw0 h2).symm
  have hχ1 : χ 1 = 1 := by
    have := hχmul 1 1
    rw [one_mul] at this
    have h3 : χ 1 * (χ 1 - 1) = 0 := by rw [mul_sub, mul_one, ← this, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exfalso
      have := hev0 1
      rw [h, zero_smul, Subgroup.coe_one, map_one, Module.End.one_apply] at this
      exact hw0 this
    · exact sub_eq_zero.mp h
  have hχne : ∀ a : A, χ a ≠ 0 := by
    intro a h
    have := hχmul a a⁻¹
    rw [mul_inv_cancel, hχ1, h, zero_mul] at this
    exact one_ne_zero this
  let ξ : G → F := fun g => if h : g ∈ A then χ ⟨g, h⟩ else 1
  have hξA : ∀ a : A, ξ a = χ a := fun a => by simp [ξ]
  have hξmul : ∀ z ∈ Z, ∀ z' ∈ Z, ξ (z * z') = ξ z * ξ z' := by
    intro z hz z' hz'
    have := hχmul ⟨z, hZA hz⟩ ⟨z', hZA hz'⟩
    have e1 := hξA ⟨z, hZA hz⟩
    have e2 := hξA ⟨z', hZA hz'⟩
    have e3 := hξA ⟨z * z', hZA (Z.mul_mem hz hz')⟩
    simp only at e1 e2 e3
    rw [e1, e2, e3]
    exact this
  have hξnt : ∃ z ∈ Z, ξ z ≠ 1 := ⟨z₀, hz₀Z, by rw [hξA ⟨z₀, hZA hz₀Z⟩]; exact hχz₀⟩
  have hξne : ∀ z ∈ Z, ξ z ≠ 0 := by
    intro z hz
    have h1 := hξA ⟨z, hZA hz⟩
    simp only at h1
    rw [h1]
    exact hχne _
  have hξreal : ∃ w : W, w ≠ 0 ∧ ∀ z ∈ Z, ρ z w = ξ z • w := by
    refine ⟨w₀, hw0, fun z hz => ?_⟩
    have h1 := hξA ⟨z, hZA hz⟩
    simp only at h1
    rw [h1]
    exact hev0 ⟨z, hZA hz⟩
  have hconj : ∀ i, ∀ a : A, (y i)⁻¹ * a * y i ∈ A := by
    intro i a
    have h1 := hZA (hcomm i a a.2)
    have : (y i)⁻¹ * (a : G) * y i = ⁅(y i)⁻¹, (a : G)⁆ * a := by
      simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact A.mul_mem h1 a.2
  let χ' : ι → A → F := fun i a => χ ⟨(y i)⁻¹ * a * y i, hconj i a⟩
  let w : ι → W := fun i => ρ (y i) w₀
  have hev : ∀ i (a : A), ρ a (w i) = χ' i a • w i := by
    intro i a
    show ρ a (ρ (y i) w₀) = χ ⟨(y i)⁻¹ * a * y i, hconj i a⟩ • ρ (y i) w₀
    have h1 : ρ a (ρ (y i) w₀) = ρ (y i) (ρ ((y i)⁻¹ * a * y i) w₀) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    rw [h1, hev0 ⟨(y i)⁻¹ * a * y i, hconj i a⟩, map_smul]
  have hw : ∀ i, w i ≠ 0 := by
    intro i h
    apply hw0
    have : ρ (y i)⁻¹ (ρ (y i) w₀) = w₀ := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← this]
    exact (congrArg (ρ (y i)⁻¹) h).trans (map_zero _)
  have hχ'inj : Function.Injective χ' := by
    intro i j hij
    by_contra hne
    obtain ⟨a, haA, ha⟩ := hdist ξ hξmul hξne hξnt hξreal i j hne
    apply ha
    have h1 := congrFun hij ⟨a, haA⟩
    simp only [χ'] at h1
    have e1 : (y i)⁻¹ * a * y i = ⁅(y i)⁻¹, a⁆ * a := by
      simp [commutatorElement_def, mul_assoc]
    have e2 : (y j)⁻¹ * a * y j = ⁅(y j)⁻¹, a⁆ * a := by
      simp [commutatorElement_def, mul_assoc]
    have hzi := hcomm i a haA
    have hzj := hcomm j a haA
    have h2 : χ ⟨(y i)⁻¹ * a * y i, hconj i ⟨a, haA⟩⟩ =
        ξ ⁅(y i)⁻¹, a⁆ * χ ⟨a, haA⟩ := by
      have := hχmul ⟨⁅(y i)⁻¹, a⁆, hZA hzi⟩ ⟨a, haA⟩
      rw [← hξA ⟨⁅(y i)⁻¹, a⁆, hZA hzi⟩] at this
      simp only at this
      rw [← this]
      congr 1
      exact Subtype.ext e1
    have h3 : χ ⟨(y j)⁻¹ * a * y j, hconj j ⟨a, haA⟩⟩ =
        ξ ⁅(y j)⁻¹, a⁆ * χ ⟨a, haA⟩ := by
      have := hχmul ⟨⁅(y j)⁻¹, a⁆, hZA hzj⟩ ⟨a, haA⟩
      rw [← hξA ⟨⁅(y j)⁻¹, a⁆, hZA hzj⟩] at this
      simp only at this
      rw [← this]
      congr 1
      exact Subtype.ext e2
    rw [h2, h3] at h1
    exact mul_right_cancel₀ (hχne ⟨a, haA⟩) h1
  have hli := linearIndependent_of_distinct_weights ρ A hA w χ' hw hev hχ'inj
  have := Fintype.ofFinite ι
  rw [Nat.card_eq_fintype_card]
  exact hli.fintype_card_le_finrank

end CFSG.SignalizerFunctorTheorem.NonLocal
