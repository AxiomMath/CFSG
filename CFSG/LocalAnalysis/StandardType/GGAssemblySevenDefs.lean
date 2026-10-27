module

public import CFSG.LocalAnalysis.StandardType.GGAssemblySixDefs
public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelLabels
public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaInnerSU33
public import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeEndRecipe
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLComp
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSp
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpComp
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordContrary
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTailAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGSLTag
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderPSLRest

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

@[expose] def GGLayerCenterCyclicRound7 : Prop :=
  GGTitsThreeCentInput ∧ GGLayerCenterCyclicExcInput

section LayerCentre

theorem ggLayerCenterCyclicInput_of_round7 (h : GGLayerCenterCyclicRound7) :
    GGLayerCenterCyclicInput :=
  ggLayerCenterCyclicInput_of_tits_exc h.1 h.2

end LayerCentre

section TableBE6

theorem ggStdSubPreInputOn_round5_of_round7 (hT : E6ThreeEnd.GGE6TwoToralInput)
    (hL : E6ThreeEnd.GGE6TwoLayerInput) (h : GGStdSubPreInputOn GGTableBOtherRound6) :
    GGStdSubPreInputOn GGTableBOtherRound5 :=
  ((ggStdSubPreInputOn_E6_three_of_twoInputs hT hL).or h).mono_split fun p lab hR hs => by
    by_cases hE6 : lab.tag = .E6 ∧ p = 3
    · exact Or.inl (ggTableBE6LabelThree_of_split hE6.1 hE6.2 hs)
    · exact Or.inr ⟨hR, hE6⟩

end TableBE6

section TableB

theorem ggStdSubPreInputOn_rest4_of_round7 (hT : E6ThreeEnd.GGE6TwoToralInput)
    (hL : E6ThreeEnd.GGE6TwoLayerInput) (hS : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (h : GGStdSubPreInputOn GGTableBOtherRound6) : GGStdSubPreInputOn GGTableBOtherRest4 :=
  ggStdSubPreInputOn_rest4_of_round5 TableBF4TwoInputs.ggF4TwoLocalEndNodeInput_holds
    TableBF4TwoInputs.ggF4TwoOuterRankInput_holds
    ⟨ggE7TwoRootFusionInput_holds, ggE8TwoRootFusionInput_holds⟩
    (ggTableBSmallRankRound5_of_round6 hS) (ggStdSubPreInputOn_round5_of_round7 hT hL h)

end TableB

section StepTwo

@[expose] def GGStepTwoToralRound7 : Prop :=
  GGSLCoordCompShapeInput ∧ GGSpCoordCompShapeInput ∧ GGSpCoordModelNonsplitInput ∧
    GGStepTwoCoordModelOn .PSU ∧ GGStepTwoCoordModelOn .POmegaPlus ∧
      GGStepTwoCoordModelOn .POmegaMinus ∧ GGStepTwoToralWitnessRestInput

theorem ggStepTwoToralRound5_of_round7 (h : GGStepTwoToralRound7) : GGStepTwoToralRound5 :=
  ⟨ggStepTwoCoordModelOn_PSL_of_compShape h.1, h.2.2.2.1,
    ggStepTwoCoordModelOn_PSp_of_compShape ggSpCoordCompInput_holds h.2.1 h.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

@[expose] def GGLayerNotDFourTwoRound7 : Prop :=
  GGLayerNotDFourTwoTag .PSU ∧ GGLayerNotDFourTwoTag .PSp ∧ GGLayerNotDFourTwoTag .POmegaPlus ∧
    GGLayerNotDFourTwoTag .POmegaMinus ∧ GGLayerNotDFourTwoTag .F4 ∧ GGLayerNotDFourTwoTag .E6 ∧
      GGLayerNotDFourTwoTag .E7 ∧ GGLayerNotDFourTwoTag .E8 ∧ GGLayerNotDFourTwoTag .twistedE6

theorem ggStepTwoAutKRestInput_of_round7 (h3 : GGAutKCanonIIIInput) (h4 : GGAutKCanonIVInput)
    (hF : GGSixFieldFiveInput) (hD : GGLayerNotDFourTwoRound7) (hC : GGStepTwoChoiceThreeInput) :
    GGStepTwoAutKRestInput :=
  ggStepTwoAutKRestInput_of_tailTags h3 h4 hF hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 hD.2.2.2.2.1
    hD.2.2.2.2.2.1 hD.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.2.2 hC

end StepTwo

section NoOffender

@[expose] def GGSixBstarFrameRound7 : Prop :=
  GGSpNonsplitFrameInput ∧ GGSixBstarMonoFrameOn GGPSUNonsplit ∧
    GGSixBstarMonoFrameOn GGPOmegaPlusNotD4Three ∧ GGSixBstarMonoFrameOn GGPOmegaMinusLabel

@[expose] def GGSixBstarNoOffenderRound7 : Prop :=
  GGSixBstarNoOffenderOn GGPOmegaPlusD4Three ∧ GGSixBstarNoOffenderAt .F4 ∧
    GGSixBstarNoOffenderAt .E6 ∧ GGSixBstarNoOffenderAt .E7 ∧ GGSixBstarNoOffenderAt .E8 ∧
      GGSixBstarNoOffenderAt .twistedE6

theorem ggSixBstarNoOffenderRestPSL_of_round7 (hF : GGSixBstarFrameRound7)
    (h : GGSixBstarNoOffenderRound7) : GGSixBstarNoOffenderRestPSL :=
  ⟨ggSixBstarNoOffenderOn_PSpNonsplit_of_frame hF.1, ggNoOffender_of_monoFrameOn hF.2.1,
    ggSixBstarNoOffenderAt_POmegaPlus_of_frame hF.2.2.1 h.1,
    ggSixBstarNoOffenderAt_POmegaMinus_of_frame hF.2.2.2, h.2⟩

end NoOffender

section NonsplitCX

@[expose] def GGNonsplitCompLiftRound7 : Prop :=
  GGNonsplitCompLiftTag .PSU ∧ GGNonsplitCompLiftTag .PSp ∧ GGNonsplitCompLiftTag .POmegaPlus ∧
    GGNonsplitCompLiftTag .POmegaMinus ∧ GGNonsplitCompLiftTag .F4 ∧ GGNonsplitCompLiftTag .E6 ∧
      GGNonsplitCompLiftTag .E7 ∧ GGNonsplitCompLiftTag .E8 ∧ GGNonsplitCompLiftTag .twistedE6

@[expose] def GGNonsplitNbrMarkingRound7 : Prop :=
  GGNonsplitNbrMarkingTag .PSU ∧ GGNonsplitNbrMarkingTag .PSp ∧
    GGNonsplitNbrMarkingTag .POmegaPlus ∧ GGNonsplitNbrMarkingTag .POmegaMinus ∧
      GGNonsplitNbrMarkingTag .F4 ∧ GGNonsplitNbrMarkingTag .E6 ∧ GGNonsplitNbrMarkingTag .E7 ∧
        GGNonsplitNbrMarkingTag .E8 ∧ GGNonsplitNbrMarkingTag .twistedE6

end NonsplitCX

section NonsplitCXTags

theorem ggSixLayerCXNonsplitInput_of_round7 (hα : GGNonsplitCompLiftRound7)
    (hβ : GGNonsplitNbrMarkingRound7) : GGSixLayerCXNonsplitInput :=
  ggSixLayerCXNonsplitInput_of_tags_PSL ⟨hα.1, hβ.1⟩ ⟨hα.2.1, hβ.2.1⟩ ⟨hα.2.2.1, hβ.2.2.1⟩
    ⟨hα.2.2.2.1, hβ.2.2.2.1⟩ ⟨hα.2.2.2.2.1, hβ.2.2.2.2.1⟩ ⟨hα.2.2.2.2.2.1, hβ.2.2.2.2.2.1⟩
    ⟨hα.2.2.2.2.2.2.1, hβ.2.2.2.2.2.2.1⟩ ⟨hα.2.2.2.2.2.2.2.1, hβ.2.2.2.2.2.2.2.1⟩
    ⟨hα.2.2.2.2.2.2.2.2, hβ.2.2.2.2.2.2.2.2⟩

end NonsplitCXTags

end CFSG.StandardType
