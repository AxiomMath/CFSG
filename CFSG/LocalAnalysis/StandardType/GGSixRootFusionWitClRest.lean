module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitClSpNs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Inputs

@[expose] def GGSixRootFusionWitClRest : Prop :=
  GGSpPlaneWitnessInputOn (fun _ f p => p ∣ 2 ^ f + 1) ∧
    GGSixRootFusionWitnessOn (fun t _ f p => t = .PSp ∧ ¬ p ∣ 2 ^ f - 1 ∧ ¬ p ∣ 2 ^ f + 1) ∧
    GGSixRootFusionWitnessOn (fun t _ _ _ => t = .POmegaPlus) ∧
    GGSixRootFusionWitnessOn (fun t _ _ _ => t = .POmegaMinus)

theorem ggSixRootFusionWitnessOn_PSp_of_rest
    (hpl : GGSpPlaneWitnessInputOn fun _ f p => p ∣ 2 ^ f + 1)
    (hrest : GGSixRootFusionWitnessOn fun t _ f p =>
      t = .PSp ∧ ¬ p ∣ 2 ^ f - 1 ∧ ¬ p ∣ 2 ^ f + 1) :
    GGSixRootFusionWitnessOn fun t _ _ _ => t = .PSp :=
  ggSixRootFusionWitnessOn_PSp_of_split ggSixRootFusionWitnessOn_PSpSplit
    (ggSixRootFusionWitnessOn_PSpNonsplit_of_plane hpl hrest)

theorem ggSixRootFusionWitnessInputFor_otherClassical_of_rest (h : GGSixRootFusionWitClRest) :
    GGSixRootFusionWitnessInputFor GGOtherClassicalTag := by
  obtain ⟨hpl, hrest, hPlus, hMinus⟩ := h
  exact ggSixRootFusionWitnessInputFor_otherClassical_of_on
    (ggSixRootFusionWitnessOn_PSp_of_rest hpl hrest) hPlus hMinus

theorem ggSixRootFusionWitClRest_parts_of_input
    (h : GGSixRootFusionWitnessInputFor GGOtherClassicalTag) :
    GGSixRootFusionWitnessOn (fun t _ f p => t = .PSp ∧ ¬ p ∣ 2 ^ f - 1 ∧ ¬ p ∣ 2 ^ f + 1) ∧
      GGSixRootFusionWitnessOn (fun t _ _ _ => t = .POmegaPlus) ∧
      GGSixRootFusionWitnessOn (fun t _ _ _ => t = .POmegaMinus) := by
  have h' := h.on
  exact ⟨h'.mono fun t _ _ _ ht => Or.inl ht.1,
    h'.mono fun t _ _ _ ht => Or.inr (Or.inr (Or.inl ht)),
    h'.mono fun t _ _ _ ht => Or.inr (Or.inr (Or.inr ht))⟩

end Inputs

end CFSG.StandardType
