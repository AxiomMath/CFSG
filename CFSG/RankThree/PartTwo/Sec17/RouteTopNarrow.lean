module

public import CFSG.RankThree.PartTwo.Sec17.RouteAssembly
public import CFSG.RankThree.PartTwo.Sec17.Item1715PrimeNarrow

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

theorem item1715_narrow_named (h1514 : Item1514S17) (h1714 : Item1714S17)
    (hP : Sec4.Item4_1PRankLargePrime) (hMeets : Claim1715Meets) (hAY : Claim1715A) :
    Item1715 :=
  item1715_of_named h1514 h1714 hMeets (HeadProof.claim1715Prime_narrow hP) hAY

section Griess

theorem item1715_of_griess_named (h1514 : Item1514S17) (h1714 : Item1714S17)
    (hGA : GriessMultipliersAllModels) (hMeets : Claim1715Meets) (hAY : Claim1715A) :
    Item1715 :=
  item1715_of_named h1514 h1714 hMeets (HeadProof.claim1715Prime_of_griess hGA) hAY

end Griess

end CFSG.RankThree.PartTwo.Sec17
