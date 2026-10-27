module

public import CFSG.RankThree.PartTwo.Sec12.Item12ResProofFree
public import CFSG.RankThree.PartTwo.Sec12.Item12Res3ProofOuter
public import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
public import CFSG.RankThree.PartTwo.Sec4.RonanK423Items
public import CFSG.RankThree.PartTwo.Sec4.Item48Proof

public section

namespace CFSG.RankThree.PartTwo.Sec12

theorem item128BarAt_of_inputs
    (h1134 : Sec11.Item1134E27N) : Item128BarAt :=
  have h45 : Sec4.Item4_5 := Sec4.rank3II_4_5
  have hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels :=
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  item128BarAt_of_free' ks128NotHJFree gap128OTwoHJ
    (KFacts.rank3II_4_22_of_items_noItem41 h45 hGA
      (Sec4.Census.rank3II_4_3_of_griess_noItem41 hGA))
    Sec4.item4_23_holds h1134 h45 (Sec4.rank3II_4_8_of h45) Sec4.Sporadic.rank3II_4_15
    KFacts.ks12NormalizerMoves

end CFSG.RankThree.PartTwo.Sec12
