module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res5Proof
public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofSp4
public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofU4
public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofCharThree
public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofExc

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Res417Three Res417Four
open Res417Five Res417Six

theorem item4_17_of_res6
        (h45 : Item4_5) (h47 : Item4_7) (h43 : Item4_3) (h46 : Item4_6)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hJ3 : Item417InJ3Rest) (hG2c : K417G2CoverCent) (hGOdd : K417NoDatumG2D4Odd)
    (hGEven : K417DatumG2D4Even) (hF4 : K417NoDatumF4) (hMcL : K417E81McL) (hG23 : K417E81G23) :
    Item4_17 :=
  item4_17_of_res5 h45 h47 h43 h46 hGA hJ3 hG2c k417NoActLThreeThree_holds
    k417NoDatumSp4Odd_holds k417DatumSp4Even_holds k417DatumU4Even_holds k417DatumU4Odd_holds
    hGOdd hGEven hF4 hMcL hG23

theorem item4_17_of_res6Narrow
        (h45 : Item4_5) (h47 : Item4_7) (h43 : Item4_3) (h46 : Item4_6)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hJ3 : Item417InJ3Rest) (hG2c : K417G2CoverCent) (hG2Odd : K417G2OddCentSU3)
    (hD4Odd : K417NoDatumD4Odd) (hG2Even : K417DatumG2Even) (hD4Even : K417DatumD4Even)
    (hRee : Sec8.ReeF4OrderThreeConj) (hTits : K417TitsCentThree) (hMcL : K417E81McL)
    (hG23 : K417E81G23) : Item4_17 :=
  item4_17_of_res6 h45 h47 h43 h46 hGA hJ3 hG2c (k417NoDatumG2D4Odd_of hG2Odd hD4Odd)
    (k417DatumG2D4Even_of hG2Even hD4Even) (k417NoDatumF4_of hRee hTits) hMcL hG23

end CFSG.RankThree.PartTwo.Sec4
