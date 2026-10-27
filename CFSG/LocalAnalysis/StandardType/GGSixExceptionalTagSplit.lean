module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitClDefs
public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFSeventeenCases

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

theorem ggExceptionalTag_iff (t : StatedLieTag) :
    GGExceptionalTag t ↔ t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨
      t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits := by
  cases t <;> simp [GGExceptionalTag, GGLinearUnitaryTag, GGOtherClassicalTag]

section Inputs

@[expose] def GGSixRootFusionWitnessExcTags : Prop :=
  (GGSixRootFusionWitnessOn fun t _ _ _ => t = .F4) ∧
    (GGSixRootFusionWitnessOn fun t _ _ _ => t = .E6) ∧
    (GGSixRootFusionWitnessOn fun t _ _ _ => t = .E7) ∧
    (GGSixRootFusionWitnessOn fun t _ _ _ => t = .E8) ∧
    (GGSixRootFusionWitnessOn fun t _ _ _ => t = .twistedE6)

theorem ggSixRootFusionWitnessOn_of_placeholder {t₀ : StatedLieTag}
    (ht₀ : t₀ = .G2 ∨ t₀ = .trialityD4 ∨ t₀ = .twistedB2 ∨ t₀ = .twistedG2 ∨ t₀ = .twistedF4 ∨
      t₀ = .Tits) :
    GGSixRootFusionWitnessOn fun t _ _ _ => t = t₀ := by
  intro G _ _ p B Bs x L D J t n f ψ ht hctx
  subst ht
  have hrk := hctx.2.2.2.1.2
  rcases ht₀ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact absurd hrk (show ¬ 2 ≤ 0 by omega)

theorem ggSixRootFusionWitnessInputFor_exceptional_of_tags (h : GGSixRootFusionWitnessExcTags) :
    GGSixRootFusionWitnessInputFor GGExceptionalTag := by
  obtain ⟨hF4, hE6, hE7, hE8, hTwE6⟩ := h
  refine ggSixRootFusionWitnessInputFor_of_on ?_
  intro G _ _ p B Bs x L D J t n f ψ ht
  rcases (ggExceptionalTag_iff t).1 ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ggSixRootFusionWitnessOn_of_placeholder (Or.inl rfl) G p B Bs x L D J _ n f ψ rfl
  · exact hF4 G p B Bs x L D J _ n f ψ rfl
  · exact hE6 G p B Bs x L D J _ n f ψ rfl
  · exact hE7 G p B Bs x L D J _ n f ψ rfl
  · exact hE8 G p B Bs x L D J _ n f ψ rfl
  · exact hTwE6 G p B Bs x L D J _ n f ψ rfl
  · exact ggSixRootFusionWitnessOn_of_placeholder (Or.inr (Or.inl rfl)) G p B Bs x L D J _ n f ψ
      rfl
  · exact ggSixRootFusionWitnessOn_of_placeholder (Or.inr (Or.inr (Or.inl rfl)))
      G p B Bs x L D J _ n f ψ rfl
  · exact ggSixRootFusionWitnessOn_of_placeholder (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      G p B Bs x L D J _ n f ψ rfl
  · exact ggSixRootFusionWitnessOn_of_placeholder (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      G p B Bs x L D J _ n f ψ rfl
  · exact ggSixRootFusionWitnessOn_of_placeholder (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      G p B Bs x L D J _ n f ψ rfl

@[expose] def GGSixSeventeenRootWitnessExcTags : Prop :=
  (GGSixSeventeenRootWitnessInputFor fun t => t = .F4) ∧
    (GGSixSeventeenRootWitnessInputFor fun t => t = .E6) ∧
    (GGSixSeventeenRootWitnessInputFor fun t => t = .E7) ∧
    (GGSixSeventeenRootWitnessInputFor fun t => t = .E8) ∧
    (GGSixSeventeenRootWitnessInputFor fun t => t = .twistedE6)

theorem ggSixSeventeenRootWitnessInputFor_of_placeholder {t₀ : StatedLieTag}
    (ht₀ : t₀ = .G2 ∨ t₀ = .trialityD4 ∨ t₀ = .twistedB2 ∨ t₀ = .twistedG2 ∨ t₀ = .twistedF4 ∨
      t₀ = .Tits) :
    GGSixSeventeenRootWitnessInputFor fun t => t = t₀ := by
  intro G _ _ p B Bs x L D J t n f ψ ht _ hctx
  subst ht
  have hrk := hctx.2.2.2.1.2
  rcases ht₀ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact absurd hrk (show ¬ 2 ≤ 0 by omega)

theorem ggSixSeventeenRootWitnessInputFor_exceptional_of_tags
    (h : GGSixSeventeenRootWitnessExcTags) :
    GGSixSeventeenRootWitnessInputFor GGExceptionalTag := by
  obtain ⟨hF4, hE6, hE7, hE8, hTwE6⟩ := h
  intro G _ _ p B Bs x L D J t n f ψ ht hne hctx
  rcases (ggExceptionalTag_iff t).1 ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ggSixSeventeenRootWitnessInputFor_of_placeholder (Or.inl rfl) G p B Bs x L D J _ n f ψ
      rfl hne hctx
  · exact hF4 G p B Bs x L D J _ n f ψ rfl hne hctx
  · exact hE6 G p B Bs x L D J _ n f ψ rfl hne hctx
  · exact hE7 G p B Bs x L D J _ n f ψ rfl hne hctx
  · exact hE8 G p B Bs x L D J _ n f ψ rfl hne hctx
  · exact hTwE6 G p B Bs x L D J _ n f ψ rfl hne hctx
  · exact ggSixSeventeenRootWitnessInputFor_of_placeholder (Or.inr (Or.inl rfl))
      G p B Bs x L D J _ n f ψ rfl hne hctx
  · exact ggSixSeventeenRootWitnessInputFor_of_placeholder (Or.inr (Or.inr (Or.inl rfl)))
      G p B Bs x L D J _ n f ψ rfl hne hctx
  · exact ggSixSeventeenRootWitnessInputFor_of_placeholder
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) G p B Bs x L D J _ n f ψ rfl hne hctx
  · exact ggSixSeventeenRootWitnessInputFor_of_placeholder
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) G p B Bs x L D J _ n f ψ rfl hne hctx
  · exact ggSixSeventeenRootWitnessInputFor_of_placeholder
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) G p B Bs x L D J _ n f ψ rfl hne hctx

end Inputs

end CFSG.StandardType
