module

public import CFSG.RankThree.PartOne.S11.Outputs
public import CFSG.RankThree.PartOne.S11b.SuzPlane
public import CFSG.RankThree.PartOne.S11b.OddF4LocalRank
public import CFSG.RankThree.PartOne.S11b.Sec11Five
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoOpenAssembly

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

structure SectionTenElevenRemaining : Prop where
  oddClassical : ActualCoverOddClassicalPlaneCentralization
  oddG2 : ActualCoverOddG2PlaneCentralization
  eType : ActualCoverETypeRankThreeOnlyE6FieldTwo
  sporadicResidual : ActualCoverSporadicMovingPlaneFiveModelResidual
  ly : LyLargePrimePlaneCentralization
  j4 : J4LargePrimePlaneCentralization
  co1 : Co1ActualArbitraryCentralCoversForceTwoLocalRankFour
  hn : MaximalMovingComponentHNQuotientsExcluded
  sec68 : Sec6EightMultipliers
  suFive : SUFiveNormalizingSubgroupsContained
  sec66 : Sec6SixFieldAutomorphismPlane

theorem sectionTenElevenInspections_of_steps_simple
    (hS : SchreierFor InCatalog)
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (hr : SectionTenElevenRemaining) (horth : OrthogonalOuterPrimeTwoTrivial)
    (hopen : SporadicOuterOrderLeTwoSimple) (hKF : KF128Rank1) (h113 : Sec11Indeed.ThreeClaim)
    (h114 : Sec11Indeed.FourClaim) (hcore : Sec11Indeed.FiveClaimCore)
    (hfin : Sec11Indeed.FinalClaim) : SectionTenElevenInspections := by
  have h107 := inSec10Seven_of_inspections hS hbridge
    (tenSevenInspections_of_known hr.oddClassical hr.oddG2 oddF4ActualCoverLocalRankFour
      hr.eType hr.sporadicResidual hr.ly suzLargePrimePlaneCentralization hr.j4 hr.co1 hr.hn)
  have h108 := inSec10EightMoving_of_inspections hS hbridge hr.sec68 hr.suFive
  have h112 := inSec11Two_of_inspections hS h107 h108 hr.sec66
  exact
    { oddClassical := hr.oddClassical
      oddG2 := hr.oddG2
      oddF4 := oddF4ActualCoverLocalRankFour
      eType := hr.eType
      sporadicResidual := hr.sporadicResidual
      ly := hr.ly
      suz := suzLargePrimePlaneCentralization
      j4 := hr.j4
      co1 := hr.co1
      hn := hr.hn
      sec68 := hr.sec68
      suFive := hr.suFive
      sec66 := hr.sec66
      indeed := sec11OneIndeed_of_core_steps hS h107 h112 hKF h113 h114 hcore hfin
      outInner := catalogPrimeTwoAutomorphismsInner_of_orthogonal_simple horth hopen }

end CFSG.RankThree.PartOne
