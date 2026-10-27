module

public import CFSG.Quasithin.Vol2.Ch3E213MSp4G41

public section

namespace CFSG.Quasithin.Ch3E213M.P6B

open Matrix
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp glMat minorJ_apply uElt uMat
  glMat_uElt)

variable {k : Type} [Field k]

theorem natAct_e0 (g : antiSp k) :
    natAct g ![1, 0, 0, 0] = ![glMat (g : GL (Fin 4) k) 0 0, glMat (g : GL (Fin 4) k) 1 0,
      glMat (g : GL (Fin 4) k) 2 0, glMat (g : GL (Fin 4) k) 3 0] := by
  funext i
  fin_cases i <;> simp [natAct, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem natAct_e1 (g : antiSp k) :
    natAct g ![0, 1, 0, 0] = ![glMat (g : GL (Fin 4) k) 0 1, glMat (g : GL (Fin 4) k) 1 1,
      glMat (g : GL (Fin 4) k) 2 1, glMat (g : GL (Fin 4) k) 3 1] := by
  funext i
  fin_cases i <;> simp [natAct, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem natAct_apply_two_three (g : antiSp k) {u : Fin 4 → k} (h2 : u 2 = 0) (h3 : u 3 = 0) :
    natAct g u 2 = glMat (g : GL (Fin 4) k) 2 0 * u 0 + glMat (g : GL (Fin 4) k) 2 1 * u 1 ∧
      natAct g u 3 = glMat (g : GL (Fin 4) k) 3 0 * u 0 + glMat (g : GL (Fin 4) k) 3 1 * u 1 := by
  simp [natAct, Matrix.mulVec, dotProduct, Fin.sum_univ_four, h2, h3]

theorem inv_three_zero (g : antiSp k) :
    glMat ((g⁻¹ : antiSp k) : GL (Fin 4) k) 3 0 = glMat (g : GL (Fin 4) k) 3 0 := by
  rw [glMat_inv_eq]
  simp [Matrix.mul_apply, Fin.sum_univ_four, minorJ_apply]

variable [CharP k 2]

theorem natAct_uElt_center (b c : k) (w : Fin 4 → k) :
    natAct (uElt 0 b c 0 : antiSp k) w = ![w 0 + (c * w 3 + b * w 2), w 1 + b * w 3, w 2, w 3] := by
  funext i
  fin_cases i <;>
    simp [natAct, glMat_uElt, uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

end CFSG.Quasithin.Ch3E213M.P6B
