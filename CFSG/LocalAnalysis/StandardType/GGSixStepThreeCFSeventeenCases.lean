module

public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFSeventeenTable

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Inputs

@[expose] def GGSixSeventeenLinearWitnessInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), GGLinearUnitaryTag t →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ : Subgroup G), GGSixSeventeenPair p B Bs x L D J t f b L₁ →
        ∃ e ∈ L₁, e ∈ Bs ∧ e ≠ 1 ∧ ∃ m ∈ Subgroup.normalizer (Bs : Set G), m⁻¹ * e * m ∈ D

@[expose] def GGSixSeventeenE8SevenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), t = .E8 → f = 1 → p = 7 →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ : Subgroup G), GGSixSeventeenPair p B Bs x L D J t f b L₁ →
        ∃ L₂ : Subgroup G, IsComponentOf L₂ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) ∧
          Nat.card (Bs ⊓ Subgroup.centralizer (L₂ : Set G) : Subgroup G) ≤ p ^ 2

@[expose] def GGSixSeventeenRootWitnessInputFor (P : StatedLieTag → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), P t → ¬ (t = .E8 ∧ f = 1 ∧ p = 7) →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ : Subgroup G), GGSixSeventeenPair p B Bs x L D J t f b L₁ →
        ∃ e ∈ L₁, e ∈ Bs ∧ e ≠ 1 ∧
          ((∃ L₂ : Subgroup G, IsComponentOf L₂ (ggG0 p B x L D J ⊓ Subgroup.centralizer {e}) ∧
            Nat.card (Bs ⊓ Subgroup.centralizer (L₂ : Set G) : Subgroup G) ≤ p ^ 2) ∨
          GGSixSeventeenSixteen p B Bs x L D J t f e)

theorem ggSixSeventeenWitnessInputFor_linearUnitary (h : GGSixSeventeenLinearWitnessInput) :
    GGSixSeventeenWitnessInputFor GGLinearUnitaryTag := by
  intro G _ _ p B Bs x L D J t n f ψ ht hctx s1 b L₁ hpair
  obtain ⟨e, heL, heB, he1, m, hm, hmD⟩ := h G p B Bs x L D J t n f ψ ht hctx s1 b L₁ hpair
  exact Or.inr ⟨e, heL, Or.inl ⟨heB, he1, Or.inl ⟨m, hm, hmD⟩⟩⟩

theorem ggSixSeventeenWitnessInputFor_of_root {P : StatedLieTag → Prop}
    (hE8 : GGSixSeventeenE8SevenInput) (hR : GGSixSeventeenRootWitnessInputFor P) :
    GGSixSeventeenWitnessInputFor P := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1 b L₁ hpair
  by_cases h8 : t = .E8 ∧ f = 1 ∧ p = 7
  · exact Or.inl (hE8 G p B Bs x L D J t n f ψ h8.1 h8.2.1 h8.2.2 hctx s1 b L₁ hpair)
  · obtain ⟨e, heL, heB, he1, h15 | h16⟩ :=
      hR G p B Bs x L D J t n f ψ hP h8 hctx s1 b L₁ hpair
    · exact Or.inr ⟨e, heL, Or.inl ⟨heB, he1, Or.inr h15⟩⟩
    · exact Or.inr ⟨e, heL, Or.inr ⟨heB, he1, h16⟩⟩

theorem ggSixSeventeenWitnessInput_of_cases (hlin : GGSixSeventeenLinearWitnessInput)
    (hE8 : GGSixSeventeenE8SevenInput)
    (hcl : GGSixSeventeenRootWitnessInputFor GGOtherClassicalTag)
    (hex : GGSixSeventeenRootWitnessInputFor GGExceptionalTag) :
    GGSixSeventeenWitnessInputFor fun _ => True :=
  ggSixSeventeenWitnessInput_of_families (ggSixSeventeenWitnessInputFor_linearUnitary hlin)
    (ggSixSeventeenWitnessInputFor_of_root hE8 hcl) (ggSixSeventeenWitnessInputFor_of_root hE8 hex)

theorem ggSixLemmaSixSeventeenInput_of_finest
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hKF : GGKGroupFusionLayerInput) (hR : GGSixAutKHypRestInput)
    (hlinW : GGSixSeventeenLinearWitnessInput) (hE8 : GGSixSeventeenE8SevenInput)
    (hcl : GGSixSeventeenRootWitnessInputFor GGOtherClassicalTag)
    (hex : GGSixSeventeenRootWitnessInputFor GGExceptionalTag)
    (h610 : GGSixBstarUniqueV2Input) (h611 : GGSixLSixElevenInput)
    (h612 : GGSixLSixTwelveInput) (h613t : GGSixTrialityInput)
    (hlin : GGSixSeventeenLinearTypeInput) : GGSixLemmaSixSeventeenInput :=
  ggSixLemmaSixSeventeenInput_of_rest hSch hKF hR
    (ggSixSeventeenWitnessInput_of_cases hlinW hE8 hcl hex) h610 h611 h612 h613t hlin

end Inputs

end CFSG.StandardType
