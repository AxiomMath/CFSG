module

public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowLargePrime
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowMcLON
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowLayer
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowCensus
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowKFacts

public section

open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

namespace CFSG.RankThree.PartTwo.Sec4.Census

theorem rank3II_4_3_of_griess_noItem41
    (hGA : GriessMultipliersAllModels) : Item4_3 :=
  rank3II_4_3_of_griess_narrow41 (Item41Narrow.item4_1LargePrime_of_griess hGA)
    (Item41Narrow.item4_1ThreeCover_of_griess hGA) hGA

theorem rank3II_4_6_of_griess_noItem41
    (hGA : GriessMultipliersAllModels) (hcen : CoverCenterThreeRest) : Item4_6 :=
  rank3II_4_6_of_griess_narrow41 (Item41Narrow.item4_1LargePrime_of_griess hGA)
    (Item41Narrow.item4_1ThreeCover_of_griess hGA) hGA hcen

end CFSG.RankThree.PartTwo.Sec4.Census

namespace CFSG.RankThree.PartTwo.KFacts

theorem rank3II_4_22_of_items_noItem41
    (h45 : Sec4.Item4_5) (hGA : GriessMultipliersAllModels) (h43 : Sec4.Item4_3) :
    Sec4.Item4_22 :=
  rank3II_4_22_of_items_narrow41 h45 (Sec4.Item41Narrow.item4_1LargePrime_of_griess hGA)
    (Sec4.Item41Narrow.item4_1ThreeCover_of_griess hGA) h43

end CFSG.RankThree.PartTwo.KFacts

namespace CFSG.RankThree.PartTwo.Sec4.Item41Narrow

theorem item434LayerRanks_of_griess
    (hGA : GriessMultipliersAllModels) : Item434LayerRanks :=
  item434LayerRanks_of_narrow (item4_1LargePrime_of_griess hGA) (item4_1ThreeCover_of_griess hGA)

end CFSG.RankThree.PartTwo.Sec4.Item41Narrow
