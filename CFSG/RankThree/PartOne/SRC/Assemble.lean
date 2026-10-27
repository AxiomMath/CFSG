module

public import CFSG.RankThree.PartOne.SRC.HardL3
public import CFSG.RankThree.PartOne.SRC.HardG2Large
public import CFSG.RankThree.PartOne.SRC.HardRee
public import CFSG.RankThree.PartOne.SRC.HardD4Large
public import CFSG.RankThree.PartOne.SRC.HardRankTwoMid
public import CFSG.RankThree.PartOne.SRC.HardG2Mid
public import CFSG.RankThree.PartOne.SRC.HardD4Prime
public import CFSG.RankThree.PartOne.SRC.Nine

public section

namespace CFSG.RankThree.PartOne.SRC

open TauCeti CFSG.RankThree.PartOne.N143

section RankTwo

theorem noHardRankTwo_of_nine (h9 : NoLowTwoRankSectionFor IsHardRankTwoNineIndex) :
    NoLowTwoRankSectionFor IsHardRankTwoIndex :=
  (noLowTwoRankSectionFor_or noHardRankTwoMid h9).mono isHardRankTwoIndex_split_nine

end RankTwo

section Exceptional

theorem noHardExceptional_of_small (hG2 : NoLowTwoRankSectionFor IsHardG2SmallIndex)
    (hD4 : NoLowTwoRankSectionFor IsHardD4PrimeIndex) :
    NoLowTwoRankSectionFor IsHardExceptionalIndex :=
  (noLowTwoRankSectionFor_or noHardG2Large
    (noLowTwoRankSectionFor_or hG2
      (noLowTwoRankSectionFor_or noHardRee
        (noLowTwoRankSectionFor_or noHardD4Large hD4)))).mono isHardExceptionalIndex_split

theorem noHardG2Small_of_nine (h9 : NoLowTwoRankSectionFor IsHardG2NineIndex) :
    NoLowTwoRankSectionFor IsHardG2SmallIndex :=
  (noLowTwoRankSectionFor_or noHardG2Mid h9).mono isHardG2SmallIndex_split_nine

theorem noHardExceptional_of_nine (hG2 : NoLowTwoRankSectionFor IsHardG2NineIndex)
    (hD4 : NoLowTwoRankSectionFor IsHardD4PrimeIndex) :
    NoLowTwoRankSectionFor IsHardExceptionalIndex :=
  noHardExceptional_of_small (noHardG2Small_of_nine hG2) hD4

theorem noHardExceptional_of_g2nine (hG2 : NoLowTwoRankSectionFor IsHardG2NineIndex) :
    NoLowTwoRankSectionFor IsHardExceptionalIndex :=
  noHardExceptional_of_nine hG2 noHardD4Prime

end Exceptional

section Final

theorem noHardLowTwo_of_cover9 (h : RankFourCoverNine) :
    NoLowTwoRankSectionFor IsHardLowTwoIndex :=
  noLowTwoRankSectionFor_hard noHardL3
    (noHardRankTwo_of_nine (noHardRankTwoNine_of_cover h))
    (noHardExceptional_of_g2nine (noHardG2Nine_of_cover h))

end Final

end CFSG.RankThree.PartOne.SRC
