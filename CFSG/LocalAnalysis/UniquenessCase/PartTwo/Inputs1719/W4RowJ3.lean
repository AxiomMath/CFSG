module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowHalf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowGen
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.J3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup.Family CFSG.Blueprint CFSG.Sporadic.Schreier
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

theorem w4Thm11_1RowM_J3_holds :
    W4Thm11_1RowM .J3 := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e₀⟩ := hs
  show 6 ≤ E3.mParam Y
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  exact W4Row.le_mParam_of_gen_out2 hW hLY hLn hF hq hO2 (e₀.trans j3CarrierEquiv)
    j3P_center_eq_bot j3P_mulAut_card (k := 3) (p := 19) (q := 19) (by norm_num) (by norm_num)
    (by norm_num) (by rw [card_j3P]; norm_num)
    (by rw [CFSG.QuasithinUnique.Setup.X1.orderOf_two_zmod_19]; norm_num)
    (by rw [CFSG.QuasithinUnique.Setup.X1.orderOf_two_zmod_19]; norm_num) j3P_gen3
    j3P_outer_dihedral

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
