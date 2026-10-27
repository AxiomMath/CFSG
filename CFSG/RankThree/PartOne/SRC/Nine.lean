module

public import CFSG.RankThree.PartOne.SRC.HardL4Nine
public import CFSG.RankThree.PartOne.SLBN.U4Hard

public section

namespace CFSG.RankThree.PartOne.SRC

open TauCeti CFSG.RankThree.PartOne.N143

@[expose] def RankFourCoverU4 : Prop :=
  ∀ i : CFSGIndex, IsHardU4NineIndex i → RankFourCover 3 i.Group

@[expose] def RankFourCoverPSp4 : Prop :=
  ∀ i : CFSGIndex, IsHardPSp4NineIndex i → RankFourCover 3 i.Group

@[expose] def RankFourCoverG2 : Prop :=
  ∀ i : CFSGIndex, IsHardG2NineIndex i → RankFourCover 3 i.Group

@[expose] def RankFourCoverNine : Prop :=
  RankFourCoverPSp4 ∧ RankFourCoverG2

theorem noHardU4Nine_of_cover (h : RankFourCoverU4) : NoLowTwoRankSectionFor IsHardU4NineIndex :=
  noLowTwoRankSectionFor_of_rankFourCover fun i hi => ⟨3, Nat.prime_three, by norm_num, h i hi⟩

theorem noHardPSp4Nine_of_cover (h : RankFourCoverPSp4) :
    NoLowTwoRankSectionFor IsHardPSp4NineIndex :=
  noLowTwoRankSectionFor_of_rankFourCover fun i hi => ⟨3, Nat.prime_three, by norm_num, h i hi⟩

theorem noHardG2Nine_of_coverG2 (h : RankFourCoverG2) : NoLowTwoRankSectionFor IsHardG2NineIndex :=
  noLowTwoRankSectionFor_of_rankFourCover fun i hi => ⟨3, Nat.prime_three, by norm_num, h i hi⟩

theorem noHardG2Nine_of_cover (h : RankFourCoverNine) :
    NoLowTwoRankSectionFor IsHardG2NineIndex :=
  noHardG2Nine_of_coverG2 h.2

section U4


theorem rankFourCoverU4 : RankFourCoverU4 := fun i hi => SLBN.rankFourCover_hardU4Nine i hi

theorem noHardRankTwoNine_of_cover (h : RankFourCoverNine) :
    NoLowTwoRankSectionFor IsHardRankTwoNineIndex :=
  (noLowTwoRankSectionFor_or noHardL4Nine
    (noLowTwoRankSectionFor_or (noHardU4Nine_of_cover rankFourCoverU4)
      (noHardPSp4Nine_of_cover h.1))).mono isHardRankTwoNineIndex_split

end U4

end CFSG.RankThree.PartOne.SRC
