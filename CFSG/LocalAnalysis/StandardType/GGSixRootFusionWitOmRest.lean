module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmMinus
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitClRest

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Inputs

@[expose] def GGSixRootFusionWitOmPlusQ1 : Prop :=
  GGSixRootFusionWitnessOn fun t _ f p => t = .POmegaPlus ∧ p ∣ 2 ^ f + 1

@[expose] def GGSixRootFusionWitOmPlusRest : Prop :=
  GGSixRootFusionWitnessOn fun t _ f p => t = .POmegaPlus ∧ ¬ p ∣ 2 ^ f - 1 ∧ ¬ p ∣ 2 ^ f + 1

@[expose] def GGSixRootFusionWitOmMinusQ1 : Prop :=
  GGSixRootFusionWitnessOn fun t _ f p => t = .POmegaMinus ∧ p ∣ 2 ^ f + 1

@[expose] def GGSixRootFusionWitOmMinusRest : Prop :=
  GGSixRootFusionWitnessOn fun t _ f p => t = .POmegaMinus ∧ ¬ p ∣ 2 ^ f - 1 ∧ ¬ p ∣ 2 ^ f + 1

theorem ggSixRootFusionWitnessOn_POmegaPlus_of_parts (h₁ : GGSixRootFusionWitOmPlusQ1)
    (h₂ : GGSixRootFusionWitOmPlusRest) :
    GGSixRootFusionWitnessOn fun t _ _ _ => t = .POmegaPlus :=
  ggSixRootFusionWitnessOn_of_split (Q := fun _ _ f p => p ∣ 2 ^ f - 1)
    ggSixRootFusionWitnessOn_POmegaPlusSplit
    (ggSixRootFusionWitnessOn_of_split (Q := fun _ _ f p => p ∣ 2 ^ f + 1)
      (h₁.mono fun _ _ _ _ h => ⟨h.1.1, h.2⟩) (h₂.mono fun _ _ _ _ h => ⟨h.1.1, h.1.2, h.2⟩))

theorem ggSixRootFusionWitnessOn_POmegaMinus_of_parts (h₁ : GGSixRootFusionWitOmMinusQ1)
    (h₂ : GGSixRootFusionWitOmMinusRest) :
    GGSixRootFusionWitnessOn fun t _ _ _ => t = .POmegaMinus :=
  ggSixRootFusionWitnessOn_of_split (Q := fun _ _ f p => p ∣ 2 ^ f - 1)
    ggSixRootFusionWitnessOn_POmegaMinusSplit
    (ggSixRootFusionWitnessOn_of_split (Q := fun _ _ f p => p ∣ 2 ^ f + 1)
      (h₁.mono fun _ _ _ _ h => ⟨h.1.1, h.2⟩) (h₂.mono fun _ _ _ _ h => ⟨h.1.1, h.1.2, h.2⟩))

theorem ggSixRootFusionWitOmParts_of_rest (h : GGSixRootFusionWitClRest) :
    GGSixRootFusionWitOmPlusQ1 ∧ GGSixRootFusionWitOmPlusRest ∧ GGSixRootFusionWitOmMinusQ1 ∧
      GGSixRootFusionWitOmMinusRest :=
  ⟨h.2.2.1.mono fun _ _ _ _ ht => ht.1, h.2.2.1.mono fun _ _ _ _ ht => ht.1,
    h.2.2.2.mono fun _ _ _ _ ht => ht.1, h.2.2.2.mono fun _ _ _ _ ht => ht.1⟩

@[expose] def GGSixRootFusionWitClRestOm : Prop :=
  GGSpPlaneWitnessInputOn (fun _ f p => p ∣ 2 ^ f + 1) ∧
    GGSixRootFusionWitnessOn (fun t _ f p => t = .PSp ∧ ¬ p ∣ 2 ^ f - 1 ∧ ¬ p ∣ 2 ^ f + 1) ∧
    GGSixRootFusionWitOmPlusQ1 ∧ GGSixRootFusionWitOmPlusRest ∧ GGSixRootFusionWitOmMinusQ1 ∧
    GGSixRootFusionWitOmMinusRest

theorem ggSixRootFusionWitClRest_of_restOm (h : GGSixRootFusionWitClRestOm) :
    GGSixRootFusionWitClRest :=
  ⟨h.1, h.2.1, ggSixRootFusionWitnessOn_POmegaPlus_of_parts h.2.2.1 h.2.2.2.1,
    ggSixRootFusionWitnessOn_POmegaMinus_of_parts h.2.2.2.2.1 h.2.2.2.2.2⟩

theorem ggSixRootFusionWitClRestOm_of_rest (h : GGSixRootFusionWitClRest) :
    GGSixRootFusionWitClRestOm :=
  ⟨h.1, h.2.1, ggSixRootFusionWitOmParts_of_rest h⟩

theorem ggSixRootFusionWitnessInputFor_otherClassical_of_restOm (h : GGSixRootFusionWitClRestOm) :
    GGSixRootFusionWitnessInputFor GGOtherClassicalTag :=
  ggSixRootFusionWitnessInputFor_otherClassical_of_rest (ggSixRootFusionWitClRest_of_restOm h)

end Inputs

end CFSG.StandardType
