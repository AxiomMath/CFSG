module

public import CFSG.RankThree.PartOne.S11b.InspectionsFromSteps
public import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

theorem inSec11Two_of_remaining
    (hS : SchreierFor InCatalog) (hbridge : TauCetiCatalogBridge)
    (hr : SectionTenElevenRemaining) : InSec11Two := by
  have h107 := inSec10Seven_of_inspections hS hbridge
    (tenSevenInspections_of_known hr.oddClassical hr.oddG2 oddF4ActualCoverLocalRankFour
      hr.eType hr.sporadicResidual hr.ly suzLargePrimePlaneCentralization hr.j4 hr.co1 hr.hn)
  have h108 := inSec10EightMoving_of_inspections hS hbridge hr.sec68 hr.suFive
  exact inSec11Two_of_inspections hS h107 h108 hr.sec66

end CFSG.RankThree.PartOne
