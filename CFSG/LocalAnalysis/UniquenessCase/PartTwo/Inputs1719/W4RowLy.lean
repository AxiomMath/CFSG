module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowHalf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowAutInner
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowDihedral
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Ly
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.LyDihedral67

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup.Family CFSG.Blueprint
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

theorem orderOf_two_zmod_67 : orderOf (2 : ZMod 67) = 66 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem w4Thm11_1RowM_Ly_holds :
    W4Thm11_1RowM .Ly := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e⟩ := hs
  have hYL : Y = L := W4Row.eq_of_fstar_eq_of_autInner hLY hLn hF hq e ly_autInner
  show 33 ≤ E3.mParam Y
  have : Fact (Nat.Prime 67) := ⟨by norm_num⟩
  have h67 : 67 ∣ Nat.card (NativeSporadic.Carrier .Ly) := by
    change 67 ∣ Nat.card NativeSporadic.Ly
    rw [CFSG.Sporadic.Ly.card_Ly]
    norm_num
  exact W4Row.le_mParam_of_dihedral hW hO2 (fun t ht _ => hYL.le ht) e (p := 67) (by norm_num)
    h67 (by rw [orderOf_two_zmod_67]) ly_dihedral67

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
