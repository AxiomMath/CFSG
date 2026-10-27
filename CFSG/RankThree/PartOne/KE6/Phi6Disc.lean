module

public import CFSG.RankThree.E6.NativeTwoA2
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.Classical2.TwistedE6Phi3Torus

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Classical2
open Matrix
open scoped Matrix MatrixGroups

variable {Ω : Type} [Field Ω]

theorem entrywise_a2Equiv₁_symm (ς : Ω →+* Ω) (X : SL(3, Ω)) :
    Units.map (entrywiseHom ς) (((a2Equiv₁ Ω).symm X : subsystemGroup Tag.E6 Ω support13) :
        ModGL Tag.E6 Ω) =
      (((a2Equiv₁ Ω).symm (Matrix.SpecialLinearGroup.map ς X) :
        subsystemGroup Tag.E6 Ω support13) : ModGL Tag.E6 Ω) := by
  rw [units_map_entrywiseHom_eq_baseChangeGL]
  have hmem := baseChangeGL_mem_subsystemGroupE6 ς ((a2Equiv₁ Ω).symm X).2
  have hau : a2Mat₁ (((a2Equiv₁ Ω).symm X : subsystemGroup Tag.E6 Ω support13) :
      ModGL Tag.E6 Ω) = (X : Matrix (Fin 3) (Fin 3) Ω) := by
    have := congrArg (fun A : SL(3, Ω) => (A : Matrix (Fin 3) (Fin 3) Ω))
      (MulEquiv.apply_symm_apply (a2Equiv₁ Ω) X)
    simpa only [a2Equiv₁_apply, coe_a2Rep₁] using this
  have h : (a2Equiv₁ Ω).symm (Matrix.SpecialLinearGroup.map ς X) =
      ⟨baseChangeGL ς (((a2Equiv₁ Ω).symm X : subsystemGroup Tag.E6 Ω support13) :
        ModGL Tag.E6 Ω), hmem⟩ := by
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [a2Equiv₁_apply, coe_a2Rep₁]
    change _ = a2Mat₁ (baseChangeGL ς (((a2Equiv₁ Ω).symm X : subsystemGroup Tag.E6 Ω support13) :
      ModGL Tag.E6 Ω))
    rw [a2Mat₁_baseChangeGL ς ((a2Equiv₁ Ω).symm X).2, hau]
    rfl
  exact (congrArg Subtype.val h).symm

theorem entrywise_a2Equiv₂_symm (ς : Ω →+* Ω) (X : SL(3, Ω)) :
    Units.map (entrywiseHom ς) (((a2Equiv₂ Ω).symm X : subsystemGroup Tag.E6 Ω support56) :
        ModGL Tag.E6 Ω) =
      (((a2Equiv₂ Ω).symm (Matrix.SpecialLinearGroup.map ς X) :
        subsystemGroup Tag.E6 Ω support56) : ModGL Tag.E6 Ω) := by
  rw [units_map_entrywiseHom_eq_baseChangeGL]
  have hmem := baseChangeGL_mem_subsystemGroupE6 ς ((a2Equiv₂ Ω).symm X).2
  have hau : a2Mat₂ (((a2Equiv₂ Ω).symm X : subsystemGroup Tag.E6 Ω support56) :
      ModGL Tag.E6 Ω) = (X : Matrix (Fin 3) (Fin 3) Ω) := by
    have := congrArg (fun A : SL(3, Ω) => (A : Matrix (Fin 3) (Fin 3) Ω))
      (MulEquiv.apply_symm_apply (a2Equiv₂ Ω) X)
    simpa only [a2Equiv₂_apply, coe_a2Rep₂] using this
  have h : (a2Equiv₂ Ω).symm (Matrix.SpecialLinearGroup.map ς X) =
      ⟨baseChangeGL ς (((a2Equiv₂ Ω).symm X : subsystemGroup Tag.E6 Ω support56) :
        ModGL Tag.E6 Ω), hmem⟩ := by
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [a2Equiv₂_apply, coe_a2Rep₂]
    change _ = a2Mat₂ (baseChangeGL ς (((a2Equiv₂ Ω).symm X : subsystemGroup Tag.E6 Ω support56) :
      ModGL Tag.E6 Ω))
    rw [a2Mat₂_baseChangeGL ς ((a2Equiv₂ Ω).symm X).2, hau]
    rfl
  exact (congrArg Subtype.val h).symm

theorem entrywise_twoA2Mul (ς : Ω →+* Ω) (X Y : SL(3, Ω)) :
    Units.map (entrywiseHom ς) (twoA2Mul Ω (X, Y)) =
      twoA2Mul Ω (Matrix.SpecialLinearGroup.map ς X, Matrix.SpecialLinearGroup.map ς Y) := by
  rw [twoA2Mul_apply, twoA2Mul_apply, map_mul, entrywise_a2Equiv₁_symm, entrywise_a2Equiv₂_symm]

theorem fst_discrepancy (ς : Ω →+* Ω) (g₁ g₂ : SL(3, Ω)) (E : ModGL Tag.E6 Ω)
    (F₁ F₂ : SL(3, Ω) → SL(3, Ω) → SL(3, Ω))
    (hE : ∀ X Y : SL(3, Ω), E * twoA2Mul Ω (X, Y) * E⁻¹ = twoA2Mul Ω (F₁ X Y, F₂ X Y))
    (X₁ X₂ : SL(3, Ω))
    (hfix : (twoA2Mul Ω (g₁, g₂) * E) * Units.map (entrywiseHom ς) (twoA2Mul Ω (X₁, X₂)) *
      (twoA2Mul Ω (g₁, g₂) * E)⁻¹ = twoA2Mul Ω (X₁, X₂)) :
    ∃ z ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3) : Ωˣ →* GL (Fin 3) Ω).range,
      Matrix.SpecialLinearGroup.toGL (g₁ * F₁ (Matrix.SpecialLinearGroup.map ς X₁)
        (Matrix.SpecialLinearGroup.map ς X₂) * g₁⁻¹) = z * Matrix.SpecialLinearGroup.toGL X₁ := by
  rw [entrywise_twoA2Mul] at hfix
  set X₁' := Matrix.SpecialLinearGroup.map ς X₁
  set X₂' := Matrix.SpecialLinearGroup.map ς X₂
  have e1 : (twoA2Mul Ω (g₁, g₂) * E) * twoA2Mul Ω (X₁', X₂') * (twoA2Mul Ω (g₁, g₂) * E)⁻¹ =
      twoA2Mul Ω (g₁ * F₁ X₁' X₂' * g₁⁻¹, g₂ * F₂ X₁' X₂' * g₂⁻¹) := by
    have e2 : (twoA2Mul Ω (g₁, g₂) * E) * twoA2Mul Ω (X₁', X₂') * (twoA2Mul Ω (g₁, g₂) * E)⁻¹ =
        twoA2Mul Ω (g₁, g₂) * (E * twoA2Mul Ω (X₁', X₂') * E⁻¹) * (twoA2Mul Ω (g₁, g₂))⁻¹ := by
      group
    rw [e2, hE, ← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e1] at hfix
  have hone : twoA2Mul Ω (g₁ * F₁ X₁' X₂' * g₁⁻¹ * X₁⁻¹, g₂ * F₂ X₁' X₂' * g₂⁻¹ * X₂⁻¹) = 1 := by
    have h0 : twoA2Mul Ω (g₁ * F₁ X₁' X₂' * g₁⁻¹, g₂ * F₂ X₁' X₂' * g₂⁻¹) *
        (twoA2Mul Ω (X₁, X₂))⁻¹ = 1 := by
      rw [hfix, mul_inv_cancel]
    rw [← map_inv, ← map_mul] at h0
    exact h0
  obtain ⟨c, hc3, hc1, -⟩ := (twoA2Mul_eq_one_iff _ _).1 hone
  have hc0 : c ≠ 0 := ne_zero_of_pow_three_eq_one hc3
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0), ⟨_, rfl⟩, ?_⟩
  have hz1 : Matrix.SpecialLinearGroup.toGL (g₁ * F₁ X₁' X₂' * g₁⁻¹ * X₁⁻¹) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) := by
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hc1, Matrix.GeneralLinearGroup.coe_scalar]
    rfl
  rw [map_mul Matrix.SpecialLinearGroup.toGL (g₁ * F₁ X₁' X₂' * g₁⁻¹) X₁⁻¹, map_inv] at hz1
  exact mul_inv_eq_iff_eq_mul.1 hz1

end CFSG.RankThree.PartOne.KE6
