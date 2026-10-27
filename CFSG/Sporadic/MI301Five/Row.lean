module

public import CFSG.Sporadic.MI301Five.Cfg
public import CFSG.Sporadic.MI301Five.RowB
public import CFSG.Sporadic.MI301Five.RowR0
public import CFSG.Sporadic.MI301.Model
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveCentM
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveCentA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveCo1Bridge
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Co1Five
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Transport

public section

namespace CFSG.Sporadic.MI301Five

open CFSG.Blueprint CFSG.Open CFSG.Monster.Existence CFSG.Monster.GMS
  CFSG.HardMathSupport.Dickson.I271 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.H301


theorem i301ARow_m5_of_centFiveA (hC : CentFiveA MGriess) : I301ARow .m5 := by
  have hE : MonsterExistenceStatement MGriess :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  haveI : Finite MGriess := hE.1.1
  obtain ⟨d, hd, hinv⟩ := exists_invertedByTwoA_five hE card_nativeB
  obtain ⟨α, z, F⟩ := exists_fiveFrame hE (TabMFive.h2B_MGriess
    (TabMFive.co1FiveBound_of_inputs TabMFive.co1FiveInputs) hE card_nativeB)
    (TabMFive.hG5_MGriess hE) hd hinv (hC d hd hinv)
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
  have hrk2 : GLATwoLocalRank 5 NativeSporadic.Co1 ≤ 2 :=
    H1017.twoRankLe_five_co1 NativeSporadic.Co1 ⟨.sporadic .Co1, rfl, ⟨b⟩⟩
  have hrk : GLATwoLocalRank 5 NativeSporadic.Co1 < 3 := hrk2.trans_lt (by norm_num)
  have hL : GMSLeechCentralizer z :=
    GMSLeechCentralizer.of_isTwoBCentralizer F.orderOf_z F.twoB
  have hX := F.shape
  obtain ⟨B₁, hB, hdB, hBX⟩ := F.exists_rowB hX
  obtain ⟨hR0, hR0t, hc⟩ := F.rowR0 hL hrk hX hB hBX
  exact i301ARow_of_model (row := .m5) MGriess CFSG.Sporadic.MI301.nonempty_mGriess_equiv_sporadicM
    (F.i301ARowCfg CFSG.Sporadic.MI301.mGriess_mulAut_eq_conj hrk hB hdB hBX hR0 hR0t hc)


theorem i301ARow_m5
    : I301ARow .m5 :=
  i301ARow_m5_of_centFiveA (TabMFive.centFiveA_MGriess_res
    ⟨TabBFiveCent.tabBFiveACard_holds, TabMFive.not_seven_dvd_card_centralizer_zFive⟩
    TabMFive.co1FiveInputs)

end CFSG.Sporadic.MI301Five
