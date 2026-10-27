module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestScalar
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestTypeAOuter
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGCorFiveTwentyRestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ¬ GGTypeALabel p lab

theorem ggCorFiveTwentyWeylInputs_of_rest
    (hG : GGWeylPseudoReflGenInputOn GGCorFiveTwentyRestLabel)
    (hSc : GGWeylCentralizerScalarInputOn GGCorFiveTwentyRestLabel)
    (hO : GGCorFiveTwentyOuterInputOn GGCorFiveTwentyRestLabel) :
    GGWeylPseudoReflGenInput ∧ GGWeylCentralizerScalarInput ∧ GGCorFiveTwentyOuterInput :=
  ⟨ggWeylPseudoReflGenInput_of_rest hG, ggWeylCentralizerScalarInput_of_rest hSc,
    ggCorFiveTwentyOuterInput_of_rest hO⟩

theorem ggCorFiveTwentyInput_of_stab_rest (ha₀ : GGLNoncyclicInput) (hRL : GGPseudoReflStabInput)
    (hRO : GGPseudoReflOrbitInput) (hG : GGWeylPseudoReflGenInputOn GGCorFiveTwentyRestLabel)
    (hSc : GGWeylCentralizerScalarInputOn GGCorFiveTwentyRestLabel)
    (hO : GGCorFiveTwentyOuterInputOn GGCorFiveTwentyRestLabel) : GGCorFiveTwentyInput :=
  let h := ggCorFiveTwentyWeylInputs_of_rest hG hSc hO
  ggCorFiveTwentyInput_of_stab ha₀ hRL hRO h.1 h.2.1 h.2.2

theorem ggCorFiveTwentyInput_of_reflRest_rest (ha₀ : GGLNoncyclicInput)
    (hBL4 : GGNbrSStarInput) (hrest : GGPseudoReflStabModInputOn GGReflRestLabel)
    (hnrest : GGPseudoReflNbrStabModInputOn GGReflRestLabel) (hA : GGPseudoReflAwayInput)
    (hG : GGWeylPseudoReflGenInputOn GGCorFiveTwentyRestLabel)
    (hSc : GGWeylCentralizerScalarInputOn GGCorFiveTwentyRestLabel)
    (hO : GGCorFiveTwentyOuterInputOn GGCorFiveTwentyRestLabel) : GGCorFiveTwentyInput :=
  let h := ggCorFiveTwentyWeylInputs_of_rest hG hSc hO
  ggCorFiveTwentyInput_of_reflRest ha₀ hBL4 hrest hnrest hA h.1 h.2.1 h.2.2

end CFSG.StandardType

end
