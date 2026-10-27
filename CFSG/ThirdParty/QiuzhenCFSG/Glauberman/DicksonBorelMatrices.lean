module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonUnipotent
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSplitTorusMatrices

namespace CFSG
end CFSG
open CFSG

/-!
# Concrete Borel matrix identities for Dickson's classification
-/

namespace CFSG.Glauberman
namespace Dickson

universe u

/-- A split-torus matrix moves past an upper unipotent by scaling its
parameter by the square of the diagonal entry. -/
public theorem splitTorusSLHom_mul_unipotentSLAddChar
    {F : Type u} [Field F] (a : Fˣ) (x : F) :
    splitTorusSLHom F a * unipotentSLAddChar F x =
      unipotentSLAddChar F ((a : F) ^ 2 * x) * splitTorusSLHom F a := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitTorusSLHom_coe, unipotentSLAddChar_coe,
      Matrix.mul_apply, Fin.sum_univ_two, pow_two, mul_assoc, mul_comm]

/-- An upper-triangular determinant-one matrix factors as unipotent times
split torus. -/
public theorem eq_unipotentSLAddChar_mul_splitTorusSLHom_of_lowerLeft_eq_zero
    {F : Type u} [Field F]
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (h10 : A 1 0 = 0) :
    ∃ a : Fˣ,
      A = unipotentSLAddChar F (A 0 1 * A 0 0) * splitTorusSLHom F a := by
  have hdet := A.property
  rw [Matrix.det_fin_two] at hdet
  have had : A 0 0 * A 1 1 = 1 := by
    simpa [h10] using hdet
  have ha_zero : A 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one had
  let a : Fˣ := Units.mk0 (A 0 0) ha_zero
  have hd_inv : A 1 1 = (a⁻¹ : F) := by
    simpa [a] using eq_inv_of_mul_eq_one_right had
  refine ⟨a, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simp [unipotentSLAddChar_coe, splitTorusSLHom_coe, Matrix.mul_apply,
      Fin.sum_univ_two, a]
  · simp [unipotentSLAddChar_coe, splitTorusSLHom_coe, Matrix.mul_apply,
      Fin.sum_univ_two, a, ha_zero]
  · simpa [unipotentSLAddChar_coe, splitTorusSLHom_coe, Matrix.mul_apply,
      Fin.sum_univ_two, a] using h10
  · simpa [unipotentSLAddChar_coe, splitTorusSLHom_coe, Matrix.mul_apply,
      Fin.sum_univ_two, a] using hd_inv

end Dickson
end CFSG.Glauberman
