module

public import CFSG.RankThree.PartTwo.Sec4.Item41ScopeProof
public import CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCoverResidual
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowMcLON
public import CFSG.RankThree.PartTwo.Sec4.Item4Res5ProofFourL34
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.RankThree.PartTwo
open CFSG.ComponentClassification.TBLit (griessMultipliersAllModels_holds)

section Item44

theorem rank3II_4_4_of_griess_noItem41 : Item4_4 :=
  rank3II_4_4_of_census
    (quasisimpleCensus_of_narrow41
      (Item41Narrow.item4_1LargePrime_of_griess griessMultipliersAllModels_holds)
      (Item41Narrow.item4_1ThreeCover_of_griess griessMultipliersAllModels_holds)
      (Item41Narrow.item4_1PRankLargePrime_of_griess griessMultipliersAllModels_holds)
      (twoCoverCensus_of_residual rank3II_4_2 griessMultipliersAllModels_holds
        griessMultipliersCentralCovers sporadicTwoCoverResidual
        (TwoCoverRanks.of_open (TwoCoverRanksOpen.of_open' (TwoCoverRanksOpen'.of_open''
          twoCoverRanksOpen'')))))
    fourL34NotSLFourOdd_holds

end Item44

end CFSG.RankThree.PartTwo.Sec4.Census
