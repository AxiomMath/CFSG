module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphAction
import CFSG.LinearAlgebra.FrobeniusSemilinearBasis
import CFSG.LinearAlgebra.FrobeniusUnitaryLang

public section

namespace CFSG.StandardType.NTPlane

open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBGraphForm
open scoped MatrixGroups

private lemma ntpA2lang_toGL_map {L : Type*} [Field L] (Fr : L →+* L) (X : SL(3, L)) :
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map Fr X) =
      Matrix.GeneralLinearGroup.map Fr (Matrix.SpecialLinearGroup.toGL X) := by
  apply Units.ext
  simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, Matrix.GeneralLinearGroup.val_map_apply,
    RingHom.mapMatrix_apply]

theorem ntpA2_lang
    {f : ℕ} (hf : 1 ≤ f) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ ((2 : ℕ) ^ f)) (B : GL (Fin 3) L) (e : Bool) :
    ∃ z : GL (Fin 3) L, ∀ X : SL(3, L),
      slConjugation 3 L B (if e then slGraphAut 3 L (Matrix.SpecialLinearGroup.map Fr X)
          else Matrix.SpecialLinearGroup.map Fr X) =
        slConjugation 3 L z⁻¹ (if e then slGraphAut 3 L (Matrix.SpecialLinearGroup.map Fr
              (slConjugation 3 L z X))
          else Matrix.SpecialLinearGroup.map Fr (slConjugation 3 L z X)) := by
  have hQ : 2 ≤ 2 ^ f := by
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hf
  cases e with
  | false =>
      obtain ⟨Y, hY⟩ := CFSG.LinearAlgebra.exists_map_frobenius_eq_mul
        (n := 3) (σ := Fr) (Q := 2 ^ f) hQ hFr B
      refine ⟨Y, fun X => ?_⟩
      apply Matrix.SpecialLinearGroup.toGL_injective
      have hFY : Matrix.GeneralLinearGroup.map Fr Y = Y * B := by
        apply Units.ext
        rw [Matrix.GeneralLinearGroup.val_map_apply, Units.val_mul]
        exact hY
      simp only [Bool.false_eq_true, if_false]
      simp only [toGL_slConjugation, ntpA2lang_toGL_map Fr]
      simp only [map_mul, map_inv, hFY]
      group
  | true =>
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨Z, hZ⟩ := CFSG.LinearAlgebra.exists_mul_mul_transpose_map_frobenius_eq_one
        (p := 2) (f := f) (σ := Fr) (n := 3) hf hFr B
      refine ⟨Z, fun X => ?_⟩
      apply Matrix.SpecialLinearGroup.toGL_injective
      have hT : glGraphAut 3 L ((Matrix.GeneralLinearGroup.map Fr Z)⁻¹) = (Z * B)⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        apply Units.ext
        simp only [Units.val_mul, Units.val_one, glGraphAut_matrix, inv_inv,
          Matrix.GeneralLinearGroup.val_map_apply]
        exact hZ
      have hδFZ : glGraphAut 3 L (Matrix.GeneralLinearGroup.map Fr Z) = Z * B := by
        have h := congrArg Inv.inv hT
        rw [← map_inv (glGraphAut 3 L), inv_inv, inv_inv] at h
        exact h
      simp only [if_true]
      simp only [toGL_slConjugation, toGL_slGraphAut, ntpA2lang_toGL_map Fr]
      simp only [map_mul, map_inv, hδFZ]
      group

end CFSG.StandardType.NTPlane
