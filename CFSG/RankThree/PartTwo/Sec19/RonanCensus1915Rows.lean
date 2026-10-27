module

public import CFSG.RankThree.PartTwo.Sec19.RonanCensus1915Image
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.RankThree.PartTwo.Sec4.RonanK429Cover

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

section Census

theorem census1915_of_rowsS
    (R : Sec4.RonanK429.K429RowsS) (h41 : Sec4.Item4_1LargePrime)
    (hExc : PartOne.ExceptionalCenterSmallPrimes) : Census1915 :=
  census1915_of_item4_29 (Sec4.RonanK429.item4_29_of_rowsS R Sec4.RonanK429.k429CoverL3)
    (census1915Image_of_rowsS R h41) h41 hExc

end Census

end CFSG.RankThree.PartTwo.Sec19
