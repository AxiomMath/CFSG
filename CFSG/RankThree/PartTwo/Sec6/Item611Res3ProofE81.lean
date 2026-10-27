module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res2Proof

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def Item611E81Lift : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    4 < CFSG.Open.pRank 3 A → ∀ c ∈ A, c ≠ 1 → ∀ L ∈ lZeroStarAt A c,
      A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c →
      ∀ E ∈ collectionIn (partTwoE G) A, L ∈ lZero E → ∀ T ∈ fourGroupsMinus E, T ≤ L →
        T ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ →
      ((A ≤ L ∧ ∃ (K : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) (_ : K.Normal),
          K = ((Subgroup.zpowers c).subgroupOf L).map
            (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) ∧
          (Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸ K ≃* projSU 4 3 1) ∨
            Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸ K ≃* Blueprint.NativeSporadic.McL))) ∨
        (A = Subgroup.zpowers c ⊔ (A ⊓ L) ∧ c ∉ L ∧
          (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.McL) ∨
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 4 (GaloisField 3 1)) ∨
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 4 3 1)))) →
      ∃ t ∈ L, t ∈ Subgroup.normalizer (A : Set G) ∧ t ≠ 1 ∧ t ^ 2 = 1 ∧
        A ⊓ Subgroup.centralizer {t} ∈ partTwoE G

@[expose] def Item611E81Inv : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    4 < CFSG.Open.pRank 3 A → ∀ c ∈ A, c ≠ 1 → ∀ L ∈ lZeroStarAt A c,
      A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c →
      ∀ E ∈ collectionIn (partTwoE G) A, L ∈ lZero E → ∀ T ∈ fourGroupsMinus E, T ≤ L →
        T ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ →
      ((A ≤ L ∧ ∃ (K : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) (_ : K.Normal),
          K = ((Subgroup.zpowers c).subgroupOf L).map
            (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) ∧
          (Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸ K ≃* projSU 4 3 1) ∨
            Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸ K ≃* Blueprint.NativeSporadic.McL))) ∨
        (A = Subgroup.zpowers c ⊔ (A ⊓ L) ∧ c ∉ L ∧
          (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.McL) ∨
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 4 (GaloisField 3 1)) ∨
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 4 3 1)))) →
      ∀ t ∈ L, t ∈ Subgroup.normalizer (A : Set G) → t ≠ 1 → t ^ 2 = 1 →
        A ⊓ Subgroup.centralizer {t} ∈ partTwoE G → False

theorem item611NotE81T_of (hL : Item611E81Lift) (hI : Item611E81Inv) : Item611NotE81T := by
  intro G _ _ hst A hA hrank c hcA hc1 L hLc hCA E hE hLE T hT hTL hTθ hcase
  obtain ⟨t, htL, htN, ht1, ht2, hD⟩ :=
    hL G hst A hA hrank c hcA hc1 L hLc hCA E hE hLE T hT hTL hTθ hcase
  exact hI G hst A hA hrank c hcA hc1 L hLc hCA E hE hLE T hT hTL hTθ hcase t htL htN ht1 ht2 hD

end CFSG.RankThree.PartTwo.Sec6
