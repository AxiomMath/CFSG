module

public import CFSG.RankThree.PartTwo.Sec4.RonanK423
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.Item423
public import CFSG.RankThree.PartTwo.Sec4.RonanStep462
public import CFSG.RankThree.PartTwo.Sec4.Item49Proved
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProofJ2Model

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.ComponentClassification.TBLit (griessMultipliersAllModels_holds)

theorem item4_23_holds
    : Item4_23 :=
  CFSG.AGLEmbeddingD2.Wilson.Coordinator.item4_23_of_six (Census.rank3II_4_6_of_griess_noItem41
      griessMultipliersAllModels_holds
      (Census.coverCenterThreeRest_of griessMultipliersAllModels_holds)) k423Inner46SixLieRest_holds

theorem item4_62_holds
    : Item4_62 :=
  RonanStep462.item4_62_of_noAlt rank3II_4_5
    (Item41Narrow.item4_1LargePrime_of_griess griessMultipliersAllModels_holds)
    (KFacts.outFixCentralThreeAbelian46Rank_of_narrow41
      (Item41Narrow.item4_1LargePrime_of_griess griessMultipliersAllModels_holds)
      (Item41Narrow.item4_1ThreeCover_of_griess griessMultipliersAllModels_holds)
      (Census.rank3II_4_3_of_griess_noItem41 griessMultipliersAllModels_holds))
    rank3II_4_9 (rank3II_4_7W_of (Census.rank3II_4_6_of_griess_noItem41
        griessMultipliersAllModels_holds
        (Census.coverCenterThreeRest_of griessMultipliersAllModels_holds))) item4_23_holds step462UAlpha_holds

end CFSG.RankThree.PartTwo.Sec4
