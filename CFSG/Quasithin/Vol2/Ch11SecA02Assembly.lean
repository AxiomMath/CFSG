module

public import CFSG.Quasithin.Vol2.Ch11SecA02Eight2
public import CFSG.Quasithin.Vol2.Ch11SecA02Excl

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

theorem stmt11_0_2_of' (h701 : Stmt7_0_1) (h325 : Stmt3_2_5) (h328 : Stmt3_2_8) (h51 : AsB51)
    (h8 : Ch10.TmpL6_3_2_2_eight) (hF : Facts02) (hM24 : IsSimpleGroup ↥NativeSporadic.M24)
    (hM24c : Nat.card ↥NativeSporadic.M24 = 2 ^ 10 * 239085) : Stmt11_0_2 := by
  intro G _ _ T L I n h
  obtain ⟨hcomm, hFF⟩ := isFFModule_of_701 h701 hM24 hM24c hF.g2Adjoint h8 h
  have hVI := fsuV_eq_of_325 h325 h51 hF.l34 hF.g2Adjoint h8 ⟨hcomm, hFF⟩ h
  obtain ⟨hiso, hcases⟩ := natural_of_328 h328 hF h8 h hVI hFF
  refine ⟨hcomm, ?_, T_le_normalizer_fsuV T I, hiso, hcases⟩
  have hirr := h.fsu.irrPlus
  rw [show conjClosure L T = L from fsuL0_eq h] at hirr
  rw [hVI]
  exact ⟨hirr.1, hirr.2.1, hirr.2.2.1, hirr.2.2.2.1, hirr.2.2.2.2.1, hirr.2.2.2.2.2.1⟩

end CFSG.Quasithin.Vol2.Ch11.SecA
