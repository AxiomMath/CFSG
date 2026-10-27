module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Split

variable {G : Type} [Group G]

theorem GGInnerDiagOnLabel.mono_label {S T : ℕ → LargeEvenLabel → Prop} {p : ℕ}
    {Bs L : Subgroup G} (hST : ∀ lab, S p lab → T p lab) (h : GGInnerDiagOnLabel S p Bs L) :
    GGInnerDiagOnLabel T p Bs L :=
  largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hST _ hP.1, hP.2⟩) h

end Split

theorem ggWeylPseudoReflGenInputOn_of_split {S S₁ S₂ : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → S₁ p lab ∨ S₂ p lab) (h₁ : GGWeylPseudoReflGenInputOn S₁)
    (h₂ : GGWeylPseudoReflGenInputOn S₂) : GGWeylPseudoReflGenInputOn S := by
  intro G _ _ p B Bs x L D J hH hM
  rcases (hM.mono_label (T := fun p lab => S₁ p lab ∨ S₂ p lab) (hS p)).elim_or with h | h
  · exact h₁ G p B Bs x L D J hH h
  · exact h₂ G p B Bs x L D J hH h

theorem ggWeylCentralizerScalarInputOn_of_split {S S₁ S₂ : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → S₁ p lab ∨ S₂ p lab) (h₁ : GGWeylCentralizerScalarInputOn S₁)
    (h₂ : GGWeylCentralizerScalarInputOn S₂) : GGWeylCentralizerScalarInputOn S := by
  intro G _ _ p B Bs x L D J hH hM
  rcases (hM.mono_label (T := fun p lab => S₁ p lab ∨ S₂ p lab) (hS p)).elim_or with h | h
  · exact h₁ G p B Bs x L D J hH h
  · exact h₂ G p B Bs x L D J hH h

theorem ggCorFiveTwentyOuterInputOn_of_split {S S₁ S₂ : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → S₁ p lab ∨ S₂ p lab) (h₁ : GGCorFiveTwentyOuterInputOn S₁)
    (h₂ : GGCorFiveTwentyOuterInputOn S₂) : GGCorFiveTwentyOuterInputOn S := by
  intro G _ _ p B Bs x L D J hH hM
  rcases (hM.mono_label (T := fun p lab => S₁ p lab ∨ S₂ p lab) (hS p)).elim_or with h | h
  · exact h₁ G p B Bs x L D J hH h
  · exact h₂ G p B Bs x L D J hH h

theorem ggWeylPseudoReflGenInputOn_symplectic : GGWeylPseudoReflGenInputOn GGReflSpLabel :=
  ggWeylPseudoReflGenInputOn_of_labels fun _ _ hp hlab h =>
    (SpModel.largeEvenLabelAll_weylInputs_symplectic hp hlab h).mono
      fun _ _ _ _ ⟨r, hl, hg, _, _⟩ => ⟨r, hl, hg⟩

theorem ggWeylCentralizerScalarInputOn_symplectic :
    GGWeylCentralizerScalarInputOn GGReflSpLabel :=
  ggWeylCentralizerScalarInputOn_of_labels fun _ _ hp hlab h =>
    (SpModel.largeEvenLabelAll_weylInputs_symplectic hp hlab h).mono
      fun _ _ _ _ ⟨r, hl, _, hi, _⟩ => ⟨r, hl, hi⟩

theorem ggInnerOnWeylInputOn_symplectic : GGInnerOnWeylInputOn GGReflSpLabel :=
  ggInnerOnWeylInputOn_of_labels fun _ _ hp hlab h =>
    (SpModel.largeEvenLabelAll_weylInputs_symplectic hp hlab h).mono
      fun _ _ _ _ ⟨r, hl, hg, _, hn⟩ => ⟨r, hl, hg, hn⟩

theorem ggCorFiveTwentyOuterInputOn_symplectic : GGCorFiveTwentyOuterInputOn GGReflSpLabel :=
  ggCorFiveTwentyOuterInputOn_of_inner ggInnerOnWeylInputOn_symplectic

@[expose] def GGCorFiveTwentyRestSpLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFiveTwentyRestLabel p lab ∧ ¬ GGReflSpLabel p lab

theorem ggCorFiveTwentyWeylInputsOn_rest_of_restSp
    (hG : GGWeylPseudoReflGenInputOn GGCorFiveTwentyRestSpLabel)
    (hSc : GGWeylCentralizerScalarInputOn GGCorFiveTwentyRestSpLabel)
    (hO : GGCorFiveTwentyOuterInputOn GGCorFiveTwentyRestSpLabel) :
    GGWeylPseudoReflGenInputOn GGCorFiveTwentyRestLabel ∧
      GGWeylCentralizerScalarInputOn GGCorFiveTwentyRestLabel ∧
      GGCorFiveTwentyOuterInputOn GGCorFiveTwentyRestLabel := by
  have hsplit : ∀ p lab, GGCorFiveTwentyRestLabel p lab →
      GGReflSpLabel p lab ∨ GGCorFiveTwentyRestSpLabel p lab := fun p lab h => by
    by_cases hs : GGReflSpLabel p lab
    · exact Or.inl hs
    · exact Or.inr ⟨h, hs⟩
  exact ⟨ggWeylPseudoReflGenInputOn_of_split hsplit ggWeylPseudoReflGenInputOn_symplectic hG,
    ggWeylCentralizerScalarInputOn_of_split hsplit ggWeylCentralizerScalarInputOn_symplectic hSc,
    ggCorFiveTwentyOuterInputOn_of_split hsplit ggCorFiveTwentyOuterInputOn_symplectic hO⟩

theorem ggCorFiveTwentyWeylInputs_of_restSp
    (hG : GGWeylPseudoReflGenInputOn GGCorFiveTwentyRestSpLabel)
    (hSc : GGWeylCentralizerScalarInputOn GGCorFiveTwentyRestSpLabel)
    (hO : GGCorFiveTwentyOuterInputOn GGCorFiveTwentyRestSpLabel) :
    GGWeylPseudoReflGenInput ∧ GGWeylCentralizerScalarInput ∧ GGCorFiveTwentyOuterInput :=
  let h := ggCorFiveTwentyWeylInputsOn_rest_of_restSp hG hSc hO
  ggCorFiveTwentyWeylInputs_of_rest h.1 h.2.1 h.2.2

theorem ggCorFiveTwentyInput_of_stab_restSp (ha₀ : GGLNoncyclicInput)
    (hRL : GGPseudoReflStabInput) (hRO : GGPseudoReflOrbitInput)
    (hG : GGWeylPseudoReflGenInputOn GGCorFiveTwentyRestSpLabel)
    (hSc : GGWeylCentralizerScalarInputOn GGCorFiveTwentyRestSpLabel)
    (hO : GGCorFiveTwentyOuterInputOn GGCorFiveTwentyRestSpLabel) : GGCorFiveTwentyInput :=
  let h := ggCorFiveTwentyWeylInputsOn_rest_of_restSp hG hSc hO
  ggCorFiveTwentyInput_of_stab_rest ha₀ hRL hRO h.1 h.2.1 h.2.2

theorem ggCorFiveTwentyInput_of_reflRest_restSp (ha₀ : GGLNoncyclicInput)
    (hBL4 : GGNbrSStarInput) (hrest : GGPseudoReflStabModInputOn GGReflRestLabel)
    (hnrest : GGPseudoReflNbrStabModInputOn GGReflRestLabel) (hA : GGPseudoReflAwayInput)
    (hG : GGWeylPseudoReflGenInputOn GGCorFiveTwentyRestSpLabel)
    (hSc : GGWeylCentralizerScalarInputOn GGCorFiveTwentyRestSpLabel)
    (hO : GGCorFiveTwentyOuterInputOn GGCorFiveTwentyRestSpLabel) : GGCorFiveTwentyInput :=
  let h := ggCorFiveTwentyWeylInputsOn_rest_of_restSp hG hSc hO
  ggCorFiveTwentyInput_of_reflRest_rest ha₀ hBL4 hrest hnrest hA h.1 h.2.1 h.2.2

end CFSG.StandardType

end
