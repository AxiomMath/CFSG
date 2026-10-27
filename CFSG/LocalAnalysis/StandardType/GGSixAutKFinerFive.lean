module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

@[expose] def GGStepTwoBstarNormFiveInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ → p = 5 →
        Nonempty (↥L₁ ⧸ Subgroup.center ↥L₁ ≃* alternatingGroup (Fin 5)) →
          Bs ≤ Subgroup.normalizer (L₁ : Set G)

@[expose] def GGSixFieldFiveInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      p = 5 → 2 ≤ f

@[expose] def GGLayerNotDFourTwoInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ → 2 ≤ f →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ y : G, y ^ p = 1 → y ∈ Subgroup.normalizer (G₀ : Set G) →
      GGPsiInnerDiag (ggU t n f).D ψ y →
      ∀ C : Subgroup G, IsComponentOf C (G₀ ⊓ Subgroup.centralizer {y}) →
        ¬ LieModel (↥C ⧸ Subgroup.center ↥C) .POmegaPlus 4 2 1

end Inputs

section Proofs

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}

theorem ggAKF_pow_four_le_card_bstar (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) :
    p ^ 4 ≤ Nat.card Bs :=
  calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G :=
        Nat.pow_le_pow_right hctx.prime.pos hctx.beta.2.2.2
    _ = Nat.card B := hctx.sstar.1.2.1.symm
    _ ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.bstar.1

theorem ggStepTwo_false_of_alt_five (hN : GGStepTwoBstarNormFiveInput)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) (s1 : GGSixStepOne p B Bs x L D J)
    {b : G} {L₁ : Subgroup G} (hpair : GGStepTwoPair p B Bs x L D J b L₁) (hp5 : p = 5)
    (he : Nonempty (↥L₁ ⧸ Subgroup.center ↥L₁ ≃* alternatingGroup (Fin 5))) : False := by
  obtain ⟨e⟩ := he
  have hBsN := hN G p B Bs x L D J t n f ψ hctx s1 b L₁ hpair hp5 ⟨e⟩
  have hBsel : IsElemAbelian p Bs := hctx.bstar.2.1
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hBsP : IsPGroup 5 Bs := fun y => ⟨1, Subtype.ext (by simpa [hp5] using hBsel.2 y y.2)⟩
  have h1 := ggAKF_card_le_five_mul hBsP hBsN hpair.2.2.1.2.2.1 e
  have h2 : Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ 25 := by
    have h := hpair.2.2.2
    rw [hp5] at h
    exact h.trans (by norm_num)
  have h3 : 625 ≤ Nat.card Bs := by
    have h := ggAKF_pow_four_le_card_bstar hctx
    rw [hp5] at h
    exact le_of_eq_of_le (by norm_num) h
  omega

theorem ggStepTwo_not_dFourTwo (hF : GGSixFieldFiveInput) (hD : GGLayerNotDFourTwoInput)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) (s1 : GGSixStepOne p B Bs x L D J)
    {b : G} {L₁ : Subgroup G} (hpair : GGStepTwoPair p B Bs x L D J b L₁) (hp5 : p = 5) :
    ¬ LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .POmegaPlus 4 2 1 :=
  hD G t n f ψ _ ⟨hctx.2.2.2.1, hctx.2.2.2.2.1, hctx.2.2.2.2.2.1.1, hctx.2.2.2.2.2.1.2⟩
    (hF G p B Bs x L D J t n f ψ hctx s1 hp5) p hctx.prime
    hctx.ne_two b (hctx.bstar.2.1.2 b hpair.1) (hctx.bstar_le_normalizer hpair.1)
    (hctx.2.2.2.2.2.2.1.2 b hpair.1) L₁ hpair.2.2.1

theorem ggStepTwoAutKFiveInput_of_finer (hN : GGStepTwoBstarNormFiveInput)
    (hF : GGSixFieldFiveInput) (hD : GGLayerNotDFourTwoInput) : GGStepTwoAutKFiveInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 _ b L₁ hpair _ _ _ _ hp5 hT
  rcases hT with he | hD4
  · exact ggStepTwo_false_of_alt_five hN hctx s1 hpair hp5 he
  · exact ggStepTwo_not_dFourTwo hF hD hctx s1 hpair hp5 hD4

end Proofs

end CFSG.StandardType
