module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenInner
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenOuterHolds
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatOdd

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)

theorem sumCatalogueClausesAt_of_open {m : ℕ} (hm : 4 ≤ m) (hOdd : CatSUmOddLieAt m)
    (hSpor : CatSUmSporadicAt m) : SUmCatalogueClausesAt m :=
  ⟨catSUmAlternating, catSUmEvenInner, catSUmEvenOuterAt hm, hOdd, hSpor, catSUmCovers⟩

theorem sumCatalogueClausesAt_of_inputs {m : ℕ} (hm : 4 ≤ m)
    (hGLS : GLS3OddLieAutComponentsInput) (hX : SUmNotOddLieInputAt m)
    (hSpor : CatSUmSporadicAt m) : SUmCatalogueClausesAt m :=
  sumCatalogueClausesAt_of_open hm (catSUmOddLieAt_of_inputs hGLS hm hX) hSpor

end CFSG.SeitzReduction.UnitaryPilot
