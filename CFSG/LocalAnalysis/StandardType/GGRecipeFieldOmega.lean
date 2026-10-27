module

public import CFSG.LocalAnalysis.StandardType.GGRecipeField
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaConjLabels

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGOmegaLabel (lab : LargeEvenLabel) : Prop :=
  GGOmegaPlusLabel lab ∨ GGOmegaMinusLabel lab

theorem ggRawInnFieldOn_omega : GGRawInnFieldOn GGOmegaLabel :=
  ggRawInnFieldOn_omegaPlus.or ggRawInnFieldOn_omegaMinus

theorem ggRawFieldConjOn_omega : GGRawFieldConjOn fun _ lab => GGOmegaLabel lab :=
  ggRawFieldConjOn_omegaPlus.or ggRawFieldConjOn_omegaMinus

theorem ggRawFieldCentralOn_omega_ne_four :
    GGRawFieldCentralOn fun lab => GGOmegaLabel lab ∧ ¬ (lab.tag = .D ∧ lab.rank = 4) := by
  refine (ggRawFieldCentralOn_omegaPlus.or ggRawFieldCentralOn_omegaMinus).mono ?_
  rintro lab ⟨⟨ht, h4⟩ | h, h4'⟩
  · have : lab.rank ≠ 4 := fun h => h4' ⟨ht, h⟩
    exact Or.inl ⟨ht, by omega⟩
  · exact Or.inr h

theorem ggRawFieldCentralOn_omega (hT : PlusFourTrialityInput) :
    GGRawFieldCentralOn GGOmegaLabel := by
  refine (ggRawFieldCentralOn_omega_ne_four.or (ggRawFieldCentralOn_omegaPlusFour hT)).mono ?_
  intro lab hlab
  by_cases h4 : lab.tag = .D ∧ lab.rank = 4
  · exact Or.inr h4
  · exact Or.inl ⟨hlab, h4⟩

theorem ggRawPCyclicOn_omega_ne_four :
    GGRawPCyclicOn fun _ lab => GGOmegaLabel lab ∧ ¬ (lab.tag = .D ∧ lab.rank = 4) := by
  refine (ggRawPCyclicOn_omegaPlus.or ggRawPCyclicOn_omegaMinus).mono ?_
  rintro p lab ⟨⟨ht, h4⟩ | h, h4'⟩
  · have : lab.rank ≠ 4 := fun h => h4' ⟨ht, h⟩
    exact Or.inl ⟨ht, by omega⟩
  · exact Or.inr h

theorem ggRawPCyclicOn_omega (hT : PlusFourTrialityInput) :
    GGRawPCyclicOn fun p lab => GGOmegaLabel lab ∧ GGNotD4Three p lab := by
  refine (ggRawPCyclicOn_omega_ne_four.or (ggRawPCyclicOn_omegaPlusFour hT)).mono ?_
  rintro p lab ⟨hlab, hne⟩
  by_cases h4 : lab.tag = .D ∧ lab.rank = 4
  · exact Or.inr ⟨h4.1, h4.2, fun hp => hne ⟨h4.1, h4.2, hp⟩⟩
  · exact Or.inl ⟨hlab, h4⟩

theorem ggRawFieldConjInputExc_of_rest_omega
    (h : GGRawFieldConjOn fun p lab => ¬ (lab.tag = .triD4 ∧ p = 3) ∧
      ¬ GGRawFieldConjDoneLabel lab ∧ ¬ GGOmegaLabel lab) :
    GGRawFieldConjInputExc :=
  ggRawFieldConjInputExc_of_rest ((ggRawFieldConjOn_omega.or h).mono fun p lab ⟨hne, hlab⟩ => by
    by_cases ho : GGOmegaLabel lab
    · exact Or.inl ho
    · exact Or.inr ⟨hne, hlab, ho⟩)


theorem ggRawInnFieldInput_of_rest_omega
    (h : GGRawInnFieldOn fun lab => ¬ GGRawInnFieldDoneLabel lab ∧ ¬ GGOmegaLabel lab) :
    GGRawInnFieldInput :=
  ggRawInnFieldInput_of_rest ((ggRawInnFieldOn_omega.or h).mono fun lab hlab => by
    by_cases ho : GGOmegaLabel lab
    · exact Or.inl ho
    · exact Or.inr ⟨hlab, ho⟩)

theorem ggRawFieldCentralInput_of_rest_omega (hT : PlusFourTrialityInput)
    (h : GGRawFieldCentralOn fun lab => ¬ GGRawFieldCentralDoneLabel lab ∧ ¬ GGOmegaLabel lab) :
    GGRawFieldCentralInput :=
  ggRawFieldCentralInput_of_rest (((ggRawFieldCentralOn_omega hT).or h).mono fun lab hlab => by
    by_cases ho : GGOmegaLabel lab
    · exact Or.inl ho
    · exact Or.inr ⟨hlab, ho⟩)

theorem ggL46CyclicInput_of_rest_omega (hT : PlusFourTrialityInput)
    (h : GGRawPCyclicOn fun p lab => GGNotD4Three p lab ∧ ¬ GGRawPCyclicDoneLabel lab ∧
      ¬ GGOmegaLabel lab)
    (hD4 : GGL46CyclicD4Input) : GGL46CyclicInput :=
  ggL46CyclicInput_of_rest (((ggRawPCyclicOn_omega hT).or h).mono fun p lab ⟨hne, hlab⟩ => by
    by_cases ho : GGOmegaLabel lab
    · exact Or.inl ⟨ho, hne⟩
    · exact Or.inr ⟨hne, hlab, ho⟩) hD4

end CFSG.StandardType
