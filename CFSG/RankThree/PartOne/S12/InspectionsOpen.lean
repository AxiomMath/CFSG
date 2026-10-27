module

public import CFSG.RankThree.PartOne.S11b.InspectionsFromSteps
public import CFSG.RankThree.PartOne.S11c.Sec66
public import CFSG.RankThree.PartOne.MultRes.Sec68Closed
import CFSG.RankThree.PartOne.S11c.OddClassicalPlane
import CFSG.RankThree.PartOne.S11c.OddG2Plane
import CFSG.RankThree.PartOne.S11c.ETypeRankThree
import CFSG.RankThree.PartOne.S11c.J4Plane
import CFSG.RankThree.PartOne.S11c.Co1Cover
import CFSG.RankThree.PartOne.S11c.SuFive

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

structure SectionTenElevenOpen : Prop where
  sporadicResidual : ActualCoverSporadicMovingPlaneFiveModelResidual
  ly : LyLargePrimePlaneCentralization
  hn : MaximalMovingComponentHNQuotientsExcluded
  sec66a : EvenOuterElementIsFieldAut
  sec66b : EvenOuterPlaneNoInnerPart

theorem SectionTenElevenOpen.toRemaining
    (hS : SchreierFor InCatalog)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : SectionTenElevenOpen) : SectionTenElevenRemaining where
  oddClassical := actualCoverOddClassicalPlaneCentralization
  oddG2 := actualCoverOddG2PlaneCentralization
  eType := actualCoverETypeRankThreeOnlyE6FieldTwo
  sporadicResidual := h.sporadicResidual
  ly := h.ly
  j4 := j4LargePrimePlaneCentralization
  co1 := co1ActualArbitraryCentralCoversForceTwoLocalRankFour
  hn := h.hn
  sec68 := MultRes.sec6Eight_of_griess hGA
  suFive := suFiveNormalizingSubgroupsContained
  sec66 := sec6Six_of_inputs hS h.sec66a h.sec66b

end CFSG.RankThree.PartOne
