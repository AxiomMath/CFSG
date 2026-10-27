module

public import CFSG.RankThree.PartOne.SRC.Assemble
public import CFSG.RankThree.PartOne.SLBN.PSp4Hard
public import CFSG.RankThree.PartOne.SLBG2.Assemble

public section

namespace CFSG.RankThree.PartOne.SRC

open TauCeti CFSG.RankThree.PartOne.N143

theorem rankFourCoverPSp4 : RankFourCoverPSp4 := fun i hi => SLBN.rankFourCover_hardPSp4Nine i hi

theorem rankFourCoverNine : RankFourCoverNine := ⟨rankFourCoverPSp4, SLBG2.rankFourCoverG2⟩

theorem noHardLowTwo : NoLowTwoRankSectionFor IsHardLowTwoIndex :=
  noHardLowTwo_of_cover9 rankFourCoverNine

end CFSG.RankThree.PartOne.SRC
