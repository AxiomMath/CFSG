module

public import CFSG.RankThree.PartTwo.Sec20.SimsItem201Frontier
public import CFSG.RankThree.PartTwo.Sec19.SimsSolSevenCit
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenHolds
public import CFSG.CGT.Foote82.T66.Frontier
public import CFSG.CGT.Hall82.Leaf
public import CFSG.CGT.Harada80.Leaf
public import CFSG.GF2Type.Smith1979CharTwoKPHolds
public import CFSG.CGT.Foote81L6.MainL6

public section

namespace CFSG.RankThree.PartTwo.Sec20

theorem item201Contra1_of_stroth
    (h1730 : Sec17.Item1730) (h310 : Sec6.Item3_10)
    (hStroth : CFSG.OddStandard.HigherRank.YamadaG23.StrothSigma6) :
    Item201Contra1 := by
  obtain ⟨h6, h5, h7S⟩ := CFSG.CGT.Foote82.footeLeavesF_holds
  exact item201Contra1_of_leaves_cit h1730
    (CFSG.CGT.Harada80.lit316Harada_of_smith GF2Type.smith1979WidthsFourSixCharTwoKP_holds)
    CFSG.CGT.Hall82.lit316Hall_holds
    (Sec19.SolEven.lit316SolomonEven_of_inputs hStroth CGT.Foote81L6.footeMainL6_holds
      (Sec19.SolEven.smith1979WidthFourCharTwoKP_of_widthsFourSix
        GF2Type.smith1979WidthsFourSixCharTwoKP_holds))
    h5 h6 h7S h310

end CFSG.RankThree.PartTwo.Sec20

namespace CFSG.RankThree.PartTwo.Sec19

theorem item316_of_stroth
    (hStroth : CFSG.OddStandard.HigherRank.YamadaG23.StrothSigma6) (h310 : Sec6.Item3_10) :
    Item316 := by
  obtain ⟨h6, h5, h7S⟩ := CFSG.CGT.Foote82.footeLeavesF_holds
  exact item316_of_foote item316ScriptX_of_citMilestone
    (CFSG.CGT.Harada80.lit316Harada_of_smith GF2Type.smith1979WidthsFourSixCharTwoKP_holds)
    CFSG.CGT.Hall82.lit316Hall_holds
    (SolEven.lit316SolomonEven_of_inputs hStroth CGT.Foote81L6.footeMainL6_holds
      (SolEven.smith1979WidthFourCharTwoKP_of_widthsFourSix
        GF2Type.smith1979WidthsFourSixCharTwoKP_holds))
    SolSeven.lit316SolomonSeven_of_citMilestone h5 h6 h7S
    CFSG.CGT.PushingUpLit.LIT.Foote.footeNonsolvableSimple_holds h310

end CFSG.RankThree.PartTwo.Sec19
