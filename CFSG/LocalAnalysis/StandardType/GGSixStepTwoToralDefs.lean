module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoContrary

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

@[expose] def GGStepTwoToralWitnessOn (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
        ∃ a ∈ Bs ⊓ (Subgroup.zpowers b ⊔ L₁), a ≠ 1 ∧
          ∃ m ∈ ggG0 p B x L D J ⊓ Subgroup.normalizer (Bs : Set G), m⁻¹ * a * m ∈ D

theorem ggStepTwoToralWitnessInput_of_on (h : ∀ t, GGStepTwoToralWitnessOn t) :
    GGStepTwoToralWitnessInput :=
  fun G _ _ p B Bs x L D J t n f ψ => h t G p B Bs x L D J n f ψ

theorem GGStepTwoToralWitnessInput.on (h : GGStepTwoToralWitnessInput) (t : StatedLieTag) :
    GGStepTwoToralWitnessOn t :=
  fun G _ _ p B Bs x L D J n f ψ => h G p B Bs x L D J t n f ψ

theorem ggStepTwoToralWitnessOn_of_not_admissible {t : StatedLieTag}
    (ht : ∀ n f : ℕ, ¬ StatedLieAdmissible t n 2 f) : GGStepTwoToralWitnessOn t := by
  intro G _ _ p B Bs x L D J n f ψ hctx
  exact absurd hctx.2.2.2.1.1 (ht n f)

theorem ggStepTwoToralWitnessOn_POmegaOdd : GGStepTwoToralWitnessOn .POmegaOdd :=
  ggStepTwoToralWitnessOn_of_not_admissible fun _ _ h => h.2.2.2 rfl

theorem ggStepTwoToralWitnessOn_twistedG2 : GGStepTwoToralWitnessOn .twistedG2 :=
  ggStepTwoToralWitnessOn_of_not_admissible fun _ _ h => absurd h.2.2.2.1 (by decide)

@[expose] def GGStepTwoToralWitnessRestInput : Prop :=
  GGStepTwoToralWitnessOn .F4 ∧ GGStepTwoToralWitnessOn .E6 ∧ GGStepTwoToralWitnessOn .E7 ∧
    GGStepTwoToralWitnessOn .E8 ∧ GGStepTwoToralWitnessOn .twistedE6 ∧
    GGStepTwoToralWitnessOn .G2 ∧ GGStepTwoToralWitnessOn .trialityD4 ∧
    GGStepTwoToralWitnessOn .twistedB2 ∧ GGStepTwoToralWitnessOn .twistedF4 ∧
    GGStepTwoToralWitnessOn .Tits

theorem ggStepTwoToralWitnessInput_of_tags (hPSL : GGStepTwoToralWitnessOn .PSL)
    (hPSU : GGStepTwoToralWitnessOn .PSU) (hPSp : GGStepTwoToralWitnessOn .PSp)
    (hPlus : GGStepTwoToralWitnessOn .POmegaPlus) (hMinus : GGStepTwoToralWitnessOn .POmegaMinus)
    (hRest : GGStepTwoToralWitnessRestInput) : GGStepTwoToralWitnessInput := by
  obtain ⟨hF4, hE6, hE7, hE8, hTwE6, hG2, hD4, hB2, hTwF4, hTits⟩ := hRest
  refine ggStepTwoToralWitnessInput_of_on fun t => ?_
  cases t
  · exact hPSL
  · exact hPSU
  · exact hPSp
  · exact ggStepTwoToralWitnessOn_POmegaOdd
  · exact hPlus
  · exact hMinus
  · exact hG2
  · exact hF4
  · exact hE6
  · exact hE7
  · exact hE8
  · exact hTwE6
  · exact hD4
  · exact hB2
  · exact ggStepTwoToralWitnessOn_twistedG2
  · exact hTwF4
  · exact hTits

theorem ggStepTwoCentralizerInput_of_tags (hPSL : GGStepTwoToralWitnessOn .PSL)
    (hPSU : GGStepTwoToralWitnessOn .PSU) (hPSp : GGStepTwoToralWitnessOn .PSp)
    (hPlus : GGStepTwoToralWitnessOn .POmegaPlus) (hMinus : GGStepTwoToralWitnessOn .POmegaMinus)
    (hRest : GGStepTwoToralWitnessRestInput) : GGStepTwoCentralizerInput :=
  ggStepTwoCentralizerInput_of_fusedWitness (ggStepTwoFusedWitnessInput_of_toral
    (ggStepTwoToralWitnessInput_of_tags hPSL hPSU hPSp hPlus hMinus hRest))

end Inputs

end CFSG.StandardType
