module

public import CFSG.RankThree.PartOne.S11.TenSevenKnown
public import CFSG.RankThree.PartOne.S11.Sec11Two
public import CFSG.RankThree.PartOne.S11.Sec11One
public import CFSG.RankThree.PartOne.S11.FivePlus

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

structure SectionTenElevenInspections : Prop where
  oddClassical : ActualCoverOddClassicalPlaneCentralization
  oddG2 : ActualCoverOddG2PlaneCentralization
  oddF4 : OddF4ActualCoverLocalRankFour
  eType : ActualCoverETypeRankThreeOnlyE6FieldTwo
  sporadicResidual : ActualCoverSporadicMovingPlaneFiveModelResidual
  ly : LyLargePrimePlaneCentralization
  suz : SuzLargePrimePlaneCentralization
  j4 : J4LargePrimePlaneCentralization
  co1 : Co1ActualArbitraryCentralCoversForceTwoLocalRankFour
  hn : MaximalMovingComponentHNQuotientsExcluded
  sec68 : Sec6EightMultipliers
  suFive : SUFiveNormalizingSubgroupsContained
  sec66 : Sec6SixFieldAutomorphismPlane
  indeed : Sec11OneIndeed
  outInner : CatalogPrimeTwoAutomorphismsInner

theorem SectionTenElevenInspections.tenSeven (h : SectionTenElevenInspections) :
    TenSevenInspections :=
  tenSevenInspections_of_known h.oddClassical h.oddG2 h.oddF4 h.eType h.sporadicResidual h.ly
    h.suz h.j4 h.co1 h.hn

theorem sectionTenEleven_of_inspections (hS : SchreierFor InCatalog)
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (hI : SectionTenElevenInspections) :
    InSec10Seven ∧ InSec10EightMoving ∧ InSec10FivePlus ∧ InSec11Two ∧ Sec11One := by
  have h107 := inSec10Seven_of_inspections hS hbridge hI.tenSeven
  have h108 := inSec10EightMoving_of_inspections hS hbridge hI.sec68 hI.suFive
  have h105 := inSec10FivePlus_of_inspections hbridge hI.outInner
  exact ⟨h107, h108, h105, inSec11Two_of_inspections hS h107 h108 hI.sec66,
    sec11One_of_indeed hS h105 hI.indeed⟩

end CFSG.RankThree.PartOne
