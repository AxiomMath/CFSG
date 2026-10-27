module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflOrbit
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflNbr
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflTypeA
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflSmall
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflSp

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGReflDoneLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGReflTypeALabel p lab ∨ GGReflSpLabel p lab ∨ GGReflB2derLabel p lab

@[expose] def GGReflRestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ¬ GGReflDoneLabel p lab

theorem largeEvenLabelAll_reflBridge_done {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGReflDoneLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusReflBridge p r R I :=
  h.elim (TypeA.largeEvenLabelAll_reflBridge_typeA hp hlab) fun h' =>
    h'.elim (largeEvenLabelAll_reflBridge_symplectic hp hlab)
      (largeEvenLabelAll_reflBridge_b2der hp)

theorem ggPseudoReflStabModInputOn_done (ha₀ : GGLNoncyclicInput) :
    GGPseudoReflStabModInputOn GGReflDoneLabel :=
  ggPseudoReflStabModInputOn_of_labels ha₀ fun _ _ hp hlab h =>
    largeEvenLabelAll_reflBridge_done hp hlab h

theorem ggPseudoReflStabInput_of_rest (ha₀ : GGLNoncyclicInput)
    (hrest : GGPseudoReflStabModInputOn GGReflRestLabel) : GGPseudoReflStabInput :=
  ggPseudoReflStabInput_of_labels ha₀
    (fun _ _ hp hlab h => largeEvenLabelAll_reflBridge_done hp hlab h) hrest

theorem ggPseudoReflNbrStabModInputOn_done (hBL4 : GGNbrSStarInput) :
    GGPseudoReflNbrStabModInputOn GGReflDoneLabel :=
  ggPseudoReflNbrStabModInputOn_of_labels hBL4 fun _ _ hp hlab h =>
    largeEvenLabelAll_reflBridge_done hp hlab h

theorem ggPseudoReflNbrStabInput_of_rest (hBL4 : GGNbrSStarInput)
    (hnrest : GGPseudoReflNbrStabModInputOn GGReflRestLabel) : GGPseudoReflNbrStabInput :=
  ggPseudoReflNbrStabInput_of_labels hBL4
    (fun _ _ hp hlab h => largeEvenLabelAll_reflBridge_done hp hlab h) hnrest

theorem ggPseudoReflOrbitInput_of_rest (hBL4 : GGNbrSStarInput)
    (hnrest : GGPseudoReflNbrStabModInputOn GGReflRestLabel) (hA : GGPseudoReflAwayInput) :
    GGPseudoReflOrbitInput :=
  ggPseudoReflOrbitInput_of_nbr (ggPseudoReflNbrStabInput_of_rest hBL4 hnrest) hA

theorem ggPseudoReflOvergroupInput_of_rest (ha₀ : GGLNoncyclicInput) (hBL4 : GGNbrSStarInput)
    (hrest : GGPseudoReflStabModInputOn GGReflRestLabel)
    (hnrest : GGPseudoReflNbrStabModInputOn GGReflRestLabel) (hA : GGPseudoReflAwayInput) :
    GGPseudoReflOvergroupInput :=
  ggPseudoReflOvergroupInput_of_stab (ggPseudoReflStabInput_of_rest ha₀ hrest)
    (ggPseudoReflOrbitInput_of_rest hBL4 hnrest hA)

theorem ggCorFiveTwentyInput_of_reflRest (ha₀ : GGLNoncyclicInput) (hBL4 : GGNbrSStarInput)
    (hrest : GGPseudoReflStabModInputOn GGReflRestLabel)
    (hnrest : GGPseudoReflNbrStabModInputOn GGReflRestLabel) (hA : GGPseudoReflAwayInput)
    (hG : GGWeylPseudoReflGenInput) (hSc : GGWeylCentralizerScalarInput)
    (hO : GGCorFiveTwentyOuterInput) : GGCorFiveTwentyInput :=
  ggCorFiveTwentyInput_of_reflections ha₀
    (ggPseudoReflOvergroupInput_of_rest ha₀ hBL4 hrest hnrest hA) hG hSc hO

end CFSG.StandardType

end
