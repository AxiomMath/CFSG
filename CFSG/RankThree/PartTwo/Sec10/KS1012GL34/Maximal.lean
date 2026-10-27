module

public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Elem

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012GL34

open CFSG.Fischer
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Light
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Bridge
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Elem

theorem det_coe_inv_mul (R : Matrix (Fin 3) (Fin 3) F4) (hR : R.det = 1)
    (y : Matrix.GeneralLinearGroup (Fin 3) F4) (hy : (y : Matrix (Fin 3) (Fin 3) F4).det = 1) :
    (R⁻¹ * (y : Matrix (Fin 3) (Fin 3) F4)).det = 1 := by
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, hR, Ring.inverse_one, hy, one_mul]

theorem coe_inv_mul_unitOfDet1 (R : Matrix (Fin 3) (Fin 3) F4) (hR : R.det = 1)
    (y : Matrix.GeneralLinearGroup (Fin 3) F4) :
    ((((unitOfDet1 R hR)⁻¹ * y : Matrix.GeneralLinearGroup (Fin 3) F4)) :
        Matrix (Fin 3) (Fin 3) F4) =
      R⁻¹ * (y : Matrix (Fin 3) (Fin 3) F4) := by
  rw [Units.val_mul, Matrix.coe_units_inv, coe_unitOfDet1]

theorem T4_core {i : Fin 6} {Y : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)}
    (hPY : P i ≤ Y) {y : Matrix.GeneralLinearGroup (Fin 3) F4} (hyY : y ∈ Y)
    (hy : (y : Matrix (Fin 3) (Fin 3) F4).det = 1)
    {R : Matrix (Fin 3) (Fin 3) F4} (hR : R.det = 1)
    (hcov : ∀ v ∈ Omega i, ∃ u ∈ Omega i, ∃ c : F4, c ≠ 0 ∧
      Matrix.mulVec (y : Matrix (Fin 3) (Fin 3) F4) v = c • Matrix.mulVec R u) :
    InM Y R := by
  have hs : stabilizes i (R⁻¹ * (y : Matrix (Fin 3) (Fin 3) F4)) :=
    stabilizes_inv_mul hR hcov
  have hQP : (unitOfDet1 R hR)⁻¹ * y ∈ P i :=
    mem_P.2 ⟨by rw [coe_inv_mul_unitOfDet1]; exact det_coe_inv_mul R hR y hy,
      by rw [coe_inv_mul_unitOfDet1]; exact hs⟩
  have hgY : unitOfDet1 R hR ∈ Y := by
    have key : unitOfDet1 R hR = y * ((unitOfDet1 R hR)⁻¹ * y)⁻¹ := by group
    rw [key]
    exact Y.mul_mem hyY (Y.inv_mem (hPY hQP))
  exact ⟨unitOfDet1 R hR, hgY, coe_unitOfDet1 R hR⟩

end CFSG.RankThree.PartTwo.Sec10.KS1012GL34

end
