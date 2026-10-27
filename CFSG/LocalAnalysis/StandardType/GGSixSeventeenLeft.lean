module

public import CFSG.LocalAnalysis.StandardType.GGSixExceptionalTagSplit

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Left

@[expose] def GGSixSeventeenRootWitnessInputForLeft (P : StatedLieTag → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), P t → ¬ (t = .E8 ∧ f = 1 ∧ p = 7) →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ : Subgroup G), GGSixSeventeenPair p B Bs x L D J t f b L₁ →
        ∃ e ∈ L₁, e ∈ Bs ∧ e ≠ 1 ∧
          ∃ L₂ : Subgroup G, IsComponentOf L₂ (ggG0 p B x L D J ⊓ Subgroup.centralizer {e}) ∧
            Nat.card (Bs ⊓ Subgroup.centralizer (L₂ : Set G) : Subgroup G) ≤ p ^ 2

theorem ggSixSeventeenRootWitnessInputFor_of_left {P : StatedLieTag → Prop}
    (h : GGSixSeventeenRootWitnessInputForLeft P) : GGSixSeventeenRootWitnessInputFor P := by
  intro G _ _ p B Bs x L D J t n f ψ hP hne hctx s1 b L₁ hpair
  obtain ⟨e, heL, heB, he1, h2⟩ := h G p B Bs x L D J t n f ψ hP hne hctx s1 b L₁ hpair
  exact ⟨e, heL, heB, he1, Or.inl h2⟩

@[expose] def GGSixSeventeenRootWitnessExcTagsLeft : Prop :=
  (GGSixSeventeenRootWitnessInputForLeft fun t => t = .F4) ∧
    (GGSixSeventeenRootWitnessInputForLeft fun t => t = .E6) ∧
    (GGSixSeventeenRootWitnessInputForLeft fun t => t = .E7) ∧
    (GGSixSeventeenRootWitnessInputForLeft fun t => t = .E8) ∧
    (GGSixSeventeenRootWitnessInputForLeft fun t => t = .twistedE6)

theorem ggSixSeventeenRootWitnessExcTags_of_left (h : GGSixSeventeenRootWitnessExcTagsLeft) :
    GGSixSeventeenRootWitnessExcTags :=
  ⟨ggSixSeventeenRootWitnessInputFor_of_left h.1, ggSixSeventeenRootWitnessInputFor_of_left h.2.1,
    ggSixSeventeenRootWitnessInputFor_of_left h.2.2.1,
    ggSixSeventeenRootWitnessInputFor_of_left h.2.2.2.1,
    ggSixSeventeenRootWitnessInputFor_of_left h.2.2.2.2⟩

end Left

end CFSG.StandardType
