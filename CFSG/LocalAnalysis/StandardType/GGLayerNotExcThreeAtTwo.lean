module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoOmTag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Tags

@[expose] def GGLayerNotExcThreeAtTwoTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ) (ψ : (ggU t n 1).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n 1).D t n 1 ψ →
    ∀ y : G, y ≠ 1 → y ^ 3 = 1 → y ∈ Subgroup.normalizer (G₀ : Set G) →
      GGPsiInnerDiag (ggU t n 1).D ψ y →
      ∀ C : Subgroup G, IsComponentOf C (G₀ ⊓ Subgroup.centralizer {y}) →
        ¬ GGStepTwoExcThreeType C

theorem ggStepTwoChoiceThreeTwoTag_of_notExcThree {t : StatedLieTag}
    (h : GGLayerNotExcThreeAtTwoTag t) : GGStepTwoChoiceThreeTwoTag t := by
  intro G _ _ p B Bs x L D J n ψ hctx _ _ b L₁ hpair hp3 hexc
  subst hp3
  exact absurd hexc (h G n ψ _ hctx.presents b hpair.2.1 (hctx.2.1.2.1.2 b hpair.1)
    (hctx.2.2.2.2.2.2.1.1 hpair.1) (hctx.2.2.2.2.2.2.1.2 b hpair.1) L₁ hpair.2.2.1)

theorem ggStepTwoChoiceThreeTwoRestFive_of_vacuous (h : GGLayerNotExcThreeAtTwoTag .F4 ∧
    GGLayerNotExcThreeAtTwoTag .E6 ∧ GGLayerNotExcThreeAtTwoTag .E7 ∧ GGLayerNotExcThreeAtTwoTag .E8
    ∧ GGStepTwoChoiceThreeTwoTag .twistedE6) :
    GGStepTwoChoiceThreeTwoRestFive :=
  ⟨ggStepTwoChoiceThreeTwoTag_of_notExcThree h.1, ggStepTwoChoiceThreeTwoTag_of_notExcThree h.2.1,
    ggStepTwoChoiceThreeTwoTag_of_notExcThree h.2.2.1,
    ggStepTwoChoiceThreeTwoTag_of_notExcThree h.2.2.2.1, h.2.2.2.2⟩

end Tags

end CFSG.StandardType
