module

public import CFSG.Quasithin.Background.F7TwoInvSp4OddTorus

public section

namespace CFSG.Quasithin.F7Two

open Matrix CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {K : Type} [Field K] [CharP K 2]

@[expose] def nb : antiSp K := uElt 0 1 0 0 * (jElt * uElt 0 1 0 0 * jElt⁻¹) * uElt 0 1 0 0

@[expose] def nc : antiSp K := uElt 0 0 1 0 * (jElt * uElt 0 0 1 0 * jElt⁻¹) * uElt 0 0 1 0

theorem glMat_nb :
    glMat (nb : antiSp K).1 = !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0] := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  change uMat 0 1 0 0 * (minorJ K * uMat 0 1 0 0 * minorJ K) * uMat 0 1 0 0 = _
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp [uMat, minorJ_apply] <;> linear_combination h2

theorem glMat_nc :
    glMat (nc : antiSp K).1 = !![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0] := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  change uMat 0 0 1 0 * (minorJ K * uMat 0 0 1 0 * minorJ K) * uMat 0 0 1 0 = _
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp [uMat, minorJ_apply] <;> linear_combination h2

theorem nb_mul_uElt (s : K) :
    (nb : antiSp K) * uElt 0 0 s 0 = (jElt * uElt 0 0 0 s * jElt⁻¹) * nb := by
  refine antiSp_ext ?_
  change glMat (nb : antiSp K).1 * uMat 0 0 s 0 =
    (minorJ K * uMat 0 0 0 s * minorJ K) * glMat (nb : antiSp K).1
  rw [glMat_nb]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp [uMat, minorJ_apply]

theorem nc_mul_uElt (s : K) :
    (nc : antiSp K) * uElt 0 s 0 0 = (jElt * uElt s 0 0 0 * jElt⁻¹) * nc := by
  refine antiSp_ext ?_
  change glMat (nc : antiSp K).1 * uMat 0 s 0 0 =
    (minorJ K * uMat s 0 0 0 * minorJ K) * glMat (nc : antiSp K).1
  rw [glMat_nc]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp [uMat, minorJ_apply]

end CFSG.Quasithin.F7Two
