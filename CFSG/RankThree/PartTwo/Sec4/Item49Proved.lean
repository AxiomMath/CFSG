module

public import CFSG.RankThree.PartTwo.Sec4.Item49Closed
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowGriess
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.ComponentClassification.TBLit (griessMultipliersAllModels_holds)

theorem rank3II_4_9
    : Item4_9 :=
  rank3II_4_9_of (Census.rank3II_4_6_of_griess_noItem41 griessMultipliersAllModels_holds
    (Census.coverCenterThreeRest_of griessMultipliersAllModels_holds)) inputs49

end CFSG.RankThree.PartTwo.Sec4
