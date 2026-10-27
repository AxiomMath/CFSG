module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusCert
public import CFSG.LocalAnalysis.StandardType.GGQ2AmbModelSplitAmb
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameSplit
public import CFSG.LocalAnalysis.StandardType.GGQ2NoTwoNodeExc
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogueU
import CFSG.LocalAnalysis.StandardType.GGQ2ExcInsideMoved
import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCensusStatements
import CFSG.LocalAnalysis.StandardType.GGQ2CensusPlane
import CFSG.LocalAnalysis.StandardType.GGQ2CensusUnitFull
import CFSG.LocalAnalysis.StandardType.GGQ2CensusUnitHeart
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusMain

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly GGQ2Frame

theorem GGQ2Frame.ExcRaw.ambModelAtFrame_excRaw
    (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (m : Fin 6) : AmbModelAtFrame (excRaw m) :=
  ambModelAtFrame_of_censusCases hLB hP (rawInsideMoved_excRaw m) (censusCases_excRaw m)

theorem ambModelFromFrameInput_excCatalogue
    (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) :
    AmbModelFromFrameInput (catalogueOf classicalCatalogue excCatalogue) := by
  refine ambModelFromFrameInput_of_halves _ (fun k hk => ?_) (fun m => ?_)
  · rw [catalogueOf_classical _ _ hk]
    exact ambModelAtFrame_classical_of_census hLB hP censusCasesLin_holds censusCasesSymp_holds
      censusCasesOrth_holds censusCasesUnitFull_holds censusCasesUnitHeart_holds k hk
  · rw [catalogueOf_exceptional _ _ (k := .exceptional m) fun h => h]
    exact ExcRaw.ambModelAtFrame_excRaw hLB hP m

theorem ggQ2AmbModelOnAmb_of_placementOn {P : LargeEvenLabel → Prop}
    {catalogue : FrameKind → RawFrameData} (hpl : PlacementInputOn P catalogue)
    (hamb : AmbModelFromFrameInput catalogue) : GGQ2AmbModelOnAmb P := by
  intro G _ _ p B Bs x L D J hS hp hI1 hxL hm _ hrow hno y K hnb hr1 hr2 hW
  obtain ⟨kind, hF⟩ := hpl hS hp hm
  exact hamb hS hp hI1 hxL hrow hno hnb hr1 hr2 hW kind hF

end CFSG.StandardType

end
