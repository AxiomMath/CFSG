module

public import CFSG.LocalAnalysis.StandardType.TableC.PSpCore
public import CFSG.LocalAnalysis.StandardType.GGRemStdSubTableBHolds
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGOddLayerCores
public import CFSG.LocalAnalysis.StandardType.GGOddLayerCentreHolds
public import CFSG.LocalAnalysis.StandardType.GGLayerCentInvolCores
public import CFSG.LocalAnalysis.StandardType.GGWeylFamQuotSolvAll
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEBundle
public import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSpNbrKGRound12
public import CFSG.LocalAnalysis.StandardType.GGTwF4SUThreeRank
public import CFSG.LocalAnalysis.StandardType.GGTwE6LangRound

public section
namespace CFSG.StandardType
open CFSG.Assembly
open CFSG.Yardstones.M3f9567aba59d


theorem ggSixFieldExtTableCAt_PSp_holds : GGSixFieldExtTableCAt .PSp := by
  obtain ⟨hTE6L, hPRn, hsR, hLCm⟩ := ggRemainderStdSubTableB_proved
  have hTE6 := ggTableBTwE6Round12_of_lang hTE6L
  have hOL : GGOddLayerCores := ggOddLayerCores_iff_centre.2 ggOddLayerCentre_holds
  have hlayCores : GGLayerTagsPilotRestSixSylowCores :=
    ggLayerTagsPilotRestSixSylowCores_iff_layerCentre.2
      (ggLayerCentInvolTrivialCores_of_oddLayer hOL)
  have hlay := ggLayerTagsPilotRestSixSylow_of_cores hlayCores
  have hlcp := ggLayerInputs_of_round5 (ggLayerTagsRound5_of_six (ggLayerTagsPilotRestSix_of_sylow hlay))
  exact ggSixFieldExtTableCAt_of_known ggLNoncyclicInput_holds
    (ggSixCentreOddInput_of_layer hlcp.1 hlcp.2)
    (ggStdSubPrimeInput_of_round12 hTE6 TwF4SUThree.ggTwF4ThreeRankInput_holds hsR)
    ggSixTCKnown_PSp_holds

end CFSG.StandardType
