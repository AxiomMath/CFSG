module

public import CFSG.RankThree.PartOne.N143.SectionListFive
public import CFSG.RankThree.PartOne.N143.SectionListSporadic
public import CFSG.RankThree.PartOne.N143.AltLeaves
public import CFSG.RankThree.PartOne.N143.SectionListSporadicC
public import CFSG.RankThree.PartOne.N143.SecRankRest
public import CFSG.RankThree.PartOne.N143.HighEven
import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly TauCeti Subgroup

theorem sectionListBound_of_hard_rest
    (h68 : Sec6EightMultipliers) (hbridge : TauCetiCatalogBridge) (hT : ThreeCat)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hE : ActualCoverETypeRankThreeOnlyE6FieldTwo) (hB : CFSG.TauCetiBridge.Even.ChevalleyBridgesAll)
    (hHighEven : NoOddCentralCoverFor IsLieHighEvenIndex) (hO7 : NoOddCentralCoverFor IsLieO7Index)
    (hHard : NoLowTwoRankSectionFor IsHardLowTwoIndex)
    (hRest : NoLowTwoRankSectionFor IsLieUnlistedRestIndex) :
    SectionListBound :=
  sectionListBound_of_leaves h68 hbridge hT
      (oddCentralCoverList3For_of_rank hT oddCentralCoverRank3For_alternating)
      (lowTwoRankSectionListFor_of_rank hT lowTwoRankSectionFor_alternating)
      oddCentralCoverList3For_sporadic lowTwoRankSectionListFor_sporadic
      (oddCentralCoverList3For_lie hT (RankThree.PartTwo.Sec4.Census.tripleCoverLie_of_griess hGA)
          hHighEven hO7 hE hB) (lowTwoRankSectionListFor_lie_of_parts hGA hHard hRest)
      oddCentralCoverListFive

theorem sectionListBound_of_split
    (h68 : Sec6EightMultipliers) (hbridge : TauCetiCatalogBridge) (hT : ThreeCat)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hE : ActualCoverETypeRankThreeOnlyE6FieldTwo) (hB : CFSG.TauCetiBridge.Even.ChevalleyBridgesAll)
    (hHighEven : NoOddCentralCoverFor IsLieHighEvenIndex) (hO7 : NoOddCentralCoverFor IsLieO7Index)
    (hHard : NoLowTwoRankSectionFor IsHardLowTwoIndex)
    (h5 : TwoPowFiveFor IsLieTwoPowFiveIndex) (hLow : NoLowTwoRankSectionFor IsLieLowTwoRankIndex) :
    SectionListBound :=
  sectionListBound_of_hard_rest h68 hbridge hT hGA hE hB hHighEven hO7 hHard
    (noLowTwoRankSectionFor_rest_of_split h5 hLow)

theorem sectionListBound_of_four_leaves
    (h68 : Sec6EightMultipliers) (hbridge : TauCetiCatalogBridge) (hT : ThreeCat)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hE : ActualCoverETypeRankThreeOnlyE6FieldTwo) (hB : CFSG.TauCetiBridge.Even.ChevalleyBridgesAll)
    (hO7 : NoOddCentralCoverFor IsLieO7Index) (hHard : NoLowTwoRankSectionFor IsHardLowTwoIndex)
    (h5 : TwoPowFiveFor IsLieTwoPowFiveIndex) (hLow : NoLowTwoRankSectionFor IsLieLowTwoRankIndex) :
    SectionListBound :=
  sectionListBound_of_split h68 hbridge hT hGA hE hB noOddCentralCoverFor_highEven hO7 hHard h5 hLow

end CFSG.RankThree.PartOne.N143
