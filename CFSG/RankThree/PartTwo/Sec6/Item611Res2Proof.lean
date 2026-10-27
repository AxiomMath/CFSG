module

public import CFSG.RankThree.PartTwo.Sec21.Item211ProofTransport

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.Item211Proof
open CFSG.Assembly.RankThreeEven (projSL projSU)

section Certs

@[expose] def Item611UPlusOut : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    4 < CFSG.Open.pRank 3 A → ∀ c ∈ A, c ≠ 1 → ∀ L ∈ lZeroStarAt A c,
      A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c →
      ∀ E ∈ collectionIn (partTwoE G) A, L ∈ lZero E → ∀ T ∈ fourGroupsPlus E, False

@[expose] def Item611ChooseMinus : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    4 < CFSG.Open.pRank 3 A → ∀ c ∈ A, c ≠ 1 → ∀ L ∈ lZeroStarAt A c,
      A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c →
      ∀ E ∈ collectionIn (partTwoE G) A, ∀ T ∈ fourGroupsMinus E,
        ∃ c' ∈ A, c' ≠ 1 ∧ ∃ L' ∈ lZeroStarAt A c',
          A ⊓ thetaQuotCentralizer L' = Subgroup.zpowers c' ∧ L' ∈ lZero E ∧
          ∃ R ∈ fourGroupsMinus E, R ≤ L' ∧
            R ⊓ inSubgroup (aschbacherSolvableCore 3) L' = ⊥ ∧
            E ⊓ Subgroup.centralizer (R : Set G) = E ⊓ Subgroup.centralizer (T : Set G)

@[expose] def Item611FieldL2T : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    4 < CFSG.Open.pRank 3 A → ∀ c ∈ A, c ≠ 1 → ∀ L ∈ lZeroStarAt A c,
      A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c →
      ∀ E ∈ collectionIn (partTwoE G) A, L ∈ lZero E → ∀ T ∈ fourGroupsMinus E, T ≤ L →
        T ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ →
      (∃ e ∈ A, ∃ m : ℕ, 2 < m ∧
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * m))) ∧
        KFacts.InducesStdKind L e .field) → False

@[expose] def Item611NotG2T : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    4 < CFSG.Open.pRank 3 A → ∀ c ∈ A, c ≠ 1 → ∀ L ∈ lZeroStarAt A c,
      A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c →
      ∀ E ∈ collectionIn (partTwoE G) A, L ∈ lZero E → ∀ T ∈ fourGroupsMinus E, T ≤ L →
        T ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ →
      A = Subgroup.zpowers c ⊔ (A ⊓ L) → c ∉ L →
      Blueprint.ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .G2 3 1 → False

@[expose] def Item611NotE81T : Prop :=
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
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 4 3 1)))) → False

end Certs

end CFSG.RankThree.PartTwo.Sec6
