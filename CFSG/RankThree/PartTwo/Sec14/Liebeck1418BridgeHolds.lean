module

public import CFSG.RankThree.PartTwo.Sec14.Liebeck1418Bridge
public import CFSG.RankThree.PartTwo.Sec4.Item45Closed
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.RankThree.PartTwo.KFacts.KS44Sz
public import CFSG.RankThree.PartTwo.Sec4.Item48Proof

public section

namespace CFSG.RankThree.PartTwo.Sec14.Liebeck1418Bridge

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem step1418OffBridgeR_holds :
    Step1418OffBridgeR :=
  step1418OffBridgeR_of Sec4.rank3II_4_5 KFacts.kpSz
    (Sec4.Item41Narrow.item4_1PRankLargePrime_of_griess
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)

theorem step1418OffLayerR_of_point
    (hPt : Step1418OffPointR) : Step1418OffLayerR :=
  step1418OffLayerR_of Sec4.rank3II_4_5 (Sec4.rank3II_4_8_of Sec4.rank3II_4_5)
    step1418OffBridgeR_holds hPt

end CFSG.RankThree.PartTwo.Sec14.Liebeck1418Bridge
