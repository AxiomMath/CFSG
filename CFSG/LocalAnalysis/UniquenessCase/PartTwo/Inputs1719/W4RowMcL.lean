module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowHalf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowHeisOut
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.McL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup.Family CFSG.Blueprint CFSG.Sporadic.Schreier
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

theorem w4Thm11_1RowM_McL_holds :
    W4Thm11_1RowM .McL := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e₀⟩ := hs
  show 8 ≤ E3.mParam Y
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h2S : 2 ∣ Nat.card ↥mclP := by
    rw [card_mclP]
    norm_num
  exact W4Row.le_mParam_of_heisCfg_out2 hW hLY hLn hF hq hO2 (e₀.trans mclCarrierEquiv) h2S
    (p := 5) (n := 0) (by norm_num) (mcl_center_not_dvd hq e₀)
    (by rw [orderOf_two_zmod_five_mcl]; norm_num) mcl_heisGen mcl_outer_heis

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
