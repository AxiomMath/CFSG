module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
public import Mathlib.Algebra.Group.AddChar

namespace CFSG
end CFSG
open CFSG

/-!
# Unipotent characters for Dickson's classification

The concrete `2 × 2` matrix calculations are kept in this small module so
callers can reuse the resulting character and injectivity theorem without
elaborating finite index case splits in a large local context.
-/

namespace CFSG.Glauberman
namespace Dickson

open BenderSuzuki.MatrixGroups

universe u

/-- The upper-unitriangular additive character in `SL(2,F)`. -/
@[expose] public def unipotentSLAddChar
    (F : Type u) [Field F] :
    AddChar F (Matrix.SpecialLinearGroup (Fin 2) F) :=
  { toFun := fun a => ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩
    map_zero_eq_one' := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    map_add_eq_mul' := by
      intro a b
      apply Subtype.ext
      ext i j
      change (!![1, a + b; 0, 1] : Matrix (Fin 2) (Fin 2) F) i j =
        ((!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) F) *
          (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) F)) i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm] }

@[simp] public theorem unipotentSLAddChar_coe
    {F : Type u} [Field F] (a : F) :
    (unipotentSLAddChar F a : Matrix (Fin 2) (Fin 2) F) =
      !![1, a; 0, 1] := rfl

/-- An upper-triangular determinant-one matrix conjugates the unipotent
character by the square of its upper-left entry. -/
public theorem unipotentSLAddChar_conj_of_lowerLeft_eq_zero
    {F : Type u} [Field F]
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hA10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (t : F) :
    A * unipotentSLAddChar F t * A⁻¹ =
      unipotentSLAddChar F
        ((A : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * t) := by
  have hdet :
      (A : Matrix (Fin 2) (Fin 2) F) 0 0 *
          (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have h := A.property
    rw [Matrix.det_fin_two, hA10, mul_zero, sub_zero] at h
    exact h
  have hdet' :
      (A : Matrix (Fin 2) (Fin 2) F) 1 1 *
          (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    rw [mul_comm, hdet]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [unipotentSLAddChar_coe,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, hA10, hdet, hdet', pow_two]
  all_goals ring

/-- The upper-unitriangular additive character in `PSL(2,F)`. -/
@[expose] public def projectiveUnipotentAddChar
    (F : Type u) [Field F] :
    AddChar F (PSL2MatrixGroup F) :=
  (QuotientGroup.mk'
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).compAddChar
      (unipotentSLAddChar F)

/-- Distinct upper-unitriangular matrices remain distinct in `PSL(2,F)`. -/
public theorem projectiveUnipotentAddChar_injective
    (F : Type u) [Field F] :
    Function.Injective (projectiveUnipotentAddChar F) := by
  intro a b hab
  have hdiff : projectiveUnipotentAddChar F (a - b) = 1 := by
    rw [sub_eq_add_neg, (projectiveUnipotentAddChar F).map_add_eq_mul,
      (projectiveUnipotentAddChar F).map_neg_eq_inv, hab, mul_inv_cancel]
  have hcenter :
      unipotentSLAddChar F (a - b) ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    exact (QuotientGroup.eq_one_iff (unipotentSLAddChar F (a - b))).mp hdiff
  have hscalar :=
    Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hcenter (0 : Fin 2)
  have hab0 := congrFun (congrFun hscalar (0 : Fin 2)) (1 : Fin 2)
  apply sub_eq_zero.mp
  change (0 : F) = a - b at hab0
  exact hab0.symm

end Dickson
end CFSG.Glauberman
