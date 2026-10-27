module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1Row
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowAutInner
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowDihedral
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J1
public import CFSG.Quasithin.Background.E3AParamCard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup.X1 CFSG.Walter CFSG.Walter.J1Props

theorem w4Thm11_1Row_J1_holds : W4Thm11_1Row .J1 := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e₀⟩ := hs
  let e : (↥L ⧸ Subgroup.center ↥L) ≃* walterJ1 := e₀.trans walterJ1EquivNative.symm
  have hYL : Y = L := W4Row.eq_of_fstar_eq_of_autInner hLY hLn hF hq e walterJ1_autInner
  refine ⟨?_, ?_⟩
  · show E3.aParam Y ≤ 3
    exact E3.aParam_le_of_card_le Y fun A hA hA2 =>
      W4Row.card_le_of_sq_eq_one_of_o2Trivial hO2 (hA.trans hYL.le) hA2 e
        walterJ1_elemAbelian_le
  · show 8 ≤ E3.mParam Y
    have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact W4Row.le_mParam_of_dihedral hW hO2 (fun t ht _ => hYL.le ht) e (p := 19)
      (by norm_num) (by rw [card_walterJ1]; norm_num) (by rw [orderOf_two_zmod_19]; norm_num)
      walterJ1_dihedral

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
