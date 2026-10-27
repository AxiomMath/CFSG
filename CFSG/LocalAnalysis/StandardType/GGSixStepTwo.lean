module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

@[expose] def GGStepTwoLemmaSixThirteenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ b ∈ Bs, Subgroup.centralizer {b} ≤ ggM p B x L D J → ∀ g : G,
        g⁻¹ * b * g ∈ ggM p B x L D J → g ∈ ggM p B x L D J

@[expose] def GGStepTwoLinearFusionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    GGStepTwoLinearType p t f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
        ∃ m ∈ Subgroup.normalizer (Bs : Set G), m⁻¹ * b * m ∈ D

@[expose] def GGStepTwoSubnormalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
        IsSubnormal L₁ (Subgroup.centralizer {b})

@[expose] def GGStepTwoCentralizerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
        IsSubnormal L₁ (Subgroup.centralizer {b}) → D ⊓ (Subgroup.zpowers b ⊔ L₁) = ⊥ →
          Subgroup.centralizer {b} ≤ ggM p B x L D J

theorem ggSixStepTwoV2Input_of_inputs (h613 : GGStepTwoLemmaSixThirteenInput)
    (hA : GGStepTwoLinearFusionInput) (h614 : GGStepTwoSubnormalInput)
    (h615 : GGStepTwoCentralizerInput) : GGSixStepTwoV2Input := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 b hb hb1 L₁ hcomp hcard
  have hpair : GGStepTwoPair p B Bs x L D J b L₁ := ⟨hb, hb1, hcomp, hcard⟩
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  obtain ⟨⟨-, hBs, -⟩, -, -, -, -, ⟨hBsM, -⟩, -, hNBs⟩ := hctx.2
  by_cases hlin : GGStepTwoLinearType p t f
  · obtain ⟨m, hm, hmD⟩ := hA G p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair
    exact hpair.stepTwo_of_conj_mem s1.2.1 (hNBs hm) hmD
  · have hsn := h614 G p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair
    have hC : Subgroup.centralizer {b} ≤ ggM p B x L D J := by
      rcases (D ⊓ (Subgroup.zpowers b ⊔ L₁)).bot_or_exists_ne_one with hDR | ⟨d, hd, hd1⟩
      · exact h615 G p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair hsn hDR
      · exact hpair.centralizer_le_of_mem hBsM s1.2.1 hsn (Subgroup.mem_inf.mp hd).1 hd1
          (Subgroup.mem_inf.mp hd).2
    exact hpair.stepTwo_of_fusion hp hBs hBsM hC
      (h613 G p B Bs x L D J t n f ψ hctx s1 hlin b hb hC)

end Inputs

end CFSG.StandardType
