module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartMain
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatAssembly
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)


theorem seitzExclusion_highPSU_of_cat_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hSpor : ∀ m : ℕ, 4 ≤ m → CatSUmSporadicAt m) : SeitzExclusion HighPSU := by
  refine seitzExclusion_highPSU_of_forall
    fun G _ _ L hset n f K _ h hn hnf e t ht _ hKt => ?_
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact false_of_seitzSetting_unitary_of_cat h hset
    (sumCatalogueClausesAt_of_inputs (by omega) hGLS (CrossChar.sUmNotOddLieInputAt _)
      (hSpor _ (by omega))) e (by omega) hnf ht hKt

end CFSG.SeitzReduction.UnitaryPilot
