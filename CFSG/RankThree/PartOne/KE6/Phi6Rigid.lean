module

public import CFSG.RankThree.PartOne.KE.E6TwThreeRigid

public section

namespace CFSG.RankThree.PartOne.KE6

open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KETw3 (eq_of_central_discrepancy scalar_range_le_center
  exists_discrepancy_conj)
open scoped MatrixGroups

theorem rigid_pos {Ω : Type} [Field Ω] (τ : Ω ≃+* Ω) (k₂ : Subfield Ω) (M a : GL (Fin 3) Ω)
    (h : ∀ A : SL(3, k₂), ∃ z ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3) :
        Ωˣ →* GL (Fin 3) Ω).range,
      M * Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map τ.toRingHom
        (Matrix.SpecialLinearGroup.map k₂.subtype A)) * M⁻¹ =
        z * (a * Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map k₂.subtype A) *
          a⁻¹)) :
    ∀ t ∈ k₂, τ t = t := by
  have : Group.IsPerfect SL(3, k₂) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (le_refl 3)
  have h' := exists_discrepancy_conj (T := fun A : SL(3, k₂) => Matrix.SpecialLinearGroup.toGL
    (Matrix.SpecialLinearGroup.map τ.toRingHom (Matrix.SpecialLinearGroup.map k₂.subtype A)))
    (X := fun A : SL(3, k₂) => Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.map k₂.subtype A)) M a h
  set M₀ : GL (Fin 3) Ω := a⁻¹ * M with hM₀
  let f₁ : SL(3, k₂) →* GL (Fin 3) Ω := (MulAut.conj M₀).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.toGL.comp ((Matrix.SpecialLinearGroup.map τ.toRingHom).comp
      (Matrix.SpecialLinearGroup.map k₂.subtype)))
  let f₂ : SL(3, k₂) →* GL (Fin 3) Ω :=
    Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map k₂.subtype)
  have hf := eq_of_central_discrepancy f₁ f₂ _ scalar_range_le_center (fun A => by
    obtain ⟨z, hzZ, hz⟩ := h' A
    exact ⟨z, hzZ, by simpa [f₁, f₂, MulAut.conj_apply] using hz⟩)
  obtain ⟨-, hfix⟩ := scalar_and_eq_of_conj_map_naturalSL k₂ (le_refl 3) τ M₀ (fun X hX => by
    obtain ⟨A, rfl⟩ := hX
    have h1 := congrArg (fun g : GL (Fin 3) Ω => (g : Matrix (Fin 3) (Fin 3) Ω))
      (DFunLike.congr_fun hf A)
    simpa [f₁, f₂, MulAut.conj_apply, Units.val_mul] using h1)
  exact hfix

theorem rigid_neg {Ω : Type} [Field Ω] (τ : Ω ≃+* Ω) (k₂ : Subfield Ω) (M a : GL (Fin 3) Ω)
    (h : ∀ A : SL(3, k₂), ∃ z ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3) :
        Ωˣ →* GL (Fin 3) Ω).range,
      M * invTransposeHom (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map
        τ.toRingHom (Matrix.SpecialLinearGroup.map k₂.subtype A))) * M⁻¹ =
        z * (a * Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map k₂.subtype A) *
          a⁻¹)) :
    False := by
  have : Group.IsPerfect SL(3, k₂) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (le_refl 3)
  have h' := exists_discrepancy_conj (T := fun A : SL(3, k₂) => invTransposeHom
    (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map τ.toRingHom
      (Matrix.SpecialLinearGroup.map k₂.subtype A))))
    (X := fun A : SL(3, k₂) => Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.map k₂.subtype A)) M a h
  set M₀ : GL (Fin 3) Ω := a⁻¹ * M with hM₀
  let f₁ : SL(3, k₂) →* GL (Fin 3) Ω := (MulAut.conj M₀).toMonoidHom.comp
    (invTransposeHom.comp (Matrix.SpecialLinearGroup.toGL.comp
      ((Matrix.SpecialLinearGroup.map τ.toRingHom).comp
        (Matrix.SpecialLinearGroup.map k₂.subtype))))
  let f₂ : SL(3, k₂) →* GL (Fin 3) Ω :=
    Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map k₂.subtype)
  have hf := eq_of_central_discrepancy f₁ f₂ _ scalar_range_le_center (fun A => by
    obtain ⟨z, hzZ, hz⟩ := h' A
    exact ⟨z, hzZ, by simpa [f₁, f₂, MulAut.conj_apply] using hz⟩)
  refine not_exists_conj_map_inv_transpose_naturalSL k₂ (le_refl 3) τ ⟨M₀, fun X hX => ?_⟩
  obtain ⟨A, rfl⟩ := hX
  have h1 := congrArg (fun g : GL (Fin 3) Ω => (g : Matrix (Fin 3) (Fin 3) Ω))
    (DFunLike.congr_fun hf A)
  simpa [f₁, f₂, MulAut.conj_apply, Units.val_mul, coe_invTransposeHom,
    Matrix.coe_units_inv] using h1

end CFSG.RankThree.PartOne.KE6
