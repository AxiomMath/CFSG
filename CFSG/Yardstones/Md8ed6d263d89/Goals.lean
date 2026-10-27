module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticHolds
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.IsoPlaneMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Point.Open
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.OpenProved
public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.YS03Final
public import CFSG.LocalAnalysis.RankFourTheoremC.P5.OpenTen
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.YSZeroKFacts23
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.YSKFactsKData29

public section

namespace CFSG.Yardstones.Md8ed6d263d89

theorem ys01_fischerRankFourPending : YSFischerRankFourPending :=
  fun G _ _ => CFSG.LocalAnalysis.RankFourTheoremC.fischerRankFourPending G

theorem ys02_invariantTwoSylowRank4 :
    CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwoSylowOfD1Rank4 :=
  CFSG.LocalAnalysis.RankFourTheoremC.invariantTwoSylowOfD1Rank4_holds

theorem ys03_relativePairExclusionRank4 :
    CFSG.LocalAnalysis.RankFourTheoremC.RelativePairExclusionOfD1Rank4 :=
  CFSG.LocalAnalysis.RankFourTheoremC.relativePairExclusionOfD1Rank4_holds

theorem ys04_pNonemptyConfinement :
    YSPNonemptyConfinement :=
  CFSG.LocalAnalysis.RankFourTheoremC.P5.pNonemptyConfinement_of_componentPCoreTrivial GL83.I243.gl83ComponentPCoreTrivial_holds

theorem ys05_pPointTypeLinTwoOrUnitary :
    YSPPointTypeLinTwoOrUnitary :=
  CFSG.LocalAnalysis.RankFourTheoremC.ysPPointTypeLinTwoOrUnitary_holds

theorem ys06_pPointCentralizers :
    YSPPointCentralizers :=
  CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.ysPPointCentralizers_proved

theorem ys07_pPointFrobenius :
    YSPPointFrobenius :=
  CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.ysPPointFrobenius_of_weak_proved
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.kFactWeakClosure_holds

theorem ys08_pEmptyPlaneLocals :
    YSPEmptyPlaneLocals :=
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ysPEmptyPlaneLocals_holds

theorem ys09_pEmptyStrongOfPlaneLocals :
    YSPEmptyStrongOfPlaneLocals :=
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ysPEmptyStrongOfPlaneLocals_holds

theorem ys10_componentPCoreTrivial :
    CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial :=
  GL83.I243.gl83ComponentPCoreTrivial_holds

theorem ys11_nongenerationList :
    CFSG.LocalAnalysis.RankFourTheoremC.GL83NongenerationList :=
  CFSG.LocalAnalysis.RankFourTheoremC.gl83NongenerationList_of_componentPCoreTrivial GL83.I243.gl83ComponentPCoreTrivial_holds

theorem ys12_signalizerAut :
    CFSG.LocalAnalysis.RankFourTheoremC.GL83SignalizerAut :=
  CFSG.LocalAnalysis.RankFourTheoremC.gl83SignalizerAut_holds

theorem ys13_innerAction :
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction :=
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction.kFactInnerAction_holds

theorem ys14_weakClosure :
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactWeakClosure :=
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.kFactWeakClosure_holds

theorem ys15_i_7_13_1 :
    GL83.I_7_13_1 :=
  GL83.I713.i_7_13_1_holds

end CFSG.Yardstones.Md8ed6d263d89
