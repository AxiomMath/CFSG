module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res5ProofField

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

section Certs

@[expose] def Item611FieldL2DField : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    4 < CFSG.Open.pRank 3 A → ∀ c ∈ A, c ≠ 1 → ∀ L ∈ lZeroStarAt A c,
      A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c →
      ∀ E ∈ collectionIn (partTwoE G) A, L ∈ lZero E → ∀ T ∈ fourGroupsMinus E, T ≤ L →
        T ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ →
      (∃ e ∈ A, ∃ m : ℕ, 2 < m ∧
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * m))) ∧
        KFacts.InducesStdKind L e .field) →
      c ∈ E → ∀ d ∈ E ⊓ Subgroup.centralizer (T : Set G), d ∉ Subgroup.zpowers c →
        KFacts.InducesStdKind L d .field

@[expose] def Item611FieldL2KExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    4 < CFSG.Open.pRank 3 A → ∀ c ∈ A, c ≠ 1 → ∀ L ∈ lZeroStarAt A c,
      A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c →
      ∀ E ∈ collectionIn (partTwoE G) A, L ∈ lZero E → ∀ T ∈ fourGroupsMinus E, T ≤ L →
        T ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ →
      (∃ e ∈ A, ∃ m : ℕ, 2 < m ∧
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * m))) ∧
        KFacts.InducesStdKind L e .field) →
      c ∈ E → ∀ d ∈ E ⊓ Subgroup.centralizer (T : Set G), d ∉ Subgroup.zpowers c →
        KFacts.InducesStdKind L d .field →
        ∃ K ∈ thetaComponentsAt 3 d,
          inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K

@[expose] def Item611FieldL2SK : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    4 < CFSG.Open.pRank 3 A → ∀ c ∈ A, c ≠ 1 → ∀ L ∈ lZeroStarAt A c,
      A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c →
      ∀ E ∈ collectionIn (partTwoE G) A, L ∈ lZero E → ∀ T ∈ fourGroupsMinus E, T ≤ L →
        T ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ →
      (∃ e ∈ A, ∃ m : ℕ, 2 < m ∧
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * m))) ∧
        KFacts.InducesStdKind L e .field) →
      c ∈ E → ∀ d ∈ E ⊓ Subgroup.centralizer (T : Set G), d ∉ Subgroup.zpowers c →
        KFacts.InducesStdKind L d .field →
      ∀ S ∈ invariantPiSubgroups (Subgroup.centralizer {d} ⊓ Subgroup.centralizer (T : Set G)) E
          (piOf 2), S ≠ ⊥ → ⁅S, Subgroup.zpowers c⁆ = S →
      ∀ K ∈ thetaComponentsAt 3 d,
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K →
        S ≤ Subgroup.normalizer (K : Set G) ∧
          ¬ ⁅S, K⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K ∧ c ∉ thetaQuotCentralizer K

@[expose] def Item611FieldL2KStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    4 < CFSG.Open.pRank 3 A → ∀ c ∈ A, c ≠ 1 → ∀ L ∈ lZeroStarAt A c,
      A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c →
      ∀ E ∈ collectionIn (partTwoE G) A, L ∈ lZero E → ∀ T ∈ fourGroupsMinus E, T ≤ L →
        T ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ →
      (∃ e ∈ A, ∃ m : ℕ, 2 < m ∧
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * m))) ∧
        KFacts.InducesStdKind L e .field) →
      c ∈ E → ∀ d ∈ E ⊓ Subgroup.centralizer (T : Set G), d ∉ Subgroup.zpowers c →
        KFacts.InducesStdKind L d .field →
      ∀ S ∈ invariantPiSubgroups (Subgroup.centralizer {d} ⊓ Subgroup.centralizer (T : Set G)) E
          (piOf 2), S ≠ ⊥ → ⁅S, Subgroup.zpowers c⁆ = S →
      ∀ K ∈ thetaComponentsAt 3 d,
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K →
        S ≤ Subgroup.normalizer (K : Set G) →
        ¬ ⁅S, K⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K → c ∉ thetaQuotCentralizer K →
        A ⊓ thetaQuotCentralizer K = Subgroup.zpowers d ∧ K ∈ lZeroStarAt A d

@[expose] def Item611FieldL2KField : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    4 < CFSG.Open.pRank 3 A → ∀ c ∈ A, c ≠ 1 → ∀ L ∈ lZeroStarAt A c,
      A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c →
      ∀ E ∈ collectionIn (partTwoE G) A, L ∈ lZero E → ∀ T ∈ fourGroupsMinus E, T ≤ L →
        T ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ →
      (∃ e ∈ A, ∃ m : ℕ, 2 < m ∧
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * m))) ∧
        KFacts.InducesStdKind L e .field) →
      c ∈ E → ∀ d ∈ E ⊓ Subgroup.centralizer (T : Set G), d ∉ Subgroup.zpowers c →
        KFacts.InducesStdKind L d .field →
      ∀ K ∈ lZeroStarAt A d, A ⊓ thetaQuotCentralizer K = Subgroup.zpowers d →
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K →
        c ∉ thetaQuotCentralizer K →
        ∃ n : ℕ, 2 < n ∧
          Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSL 2 (GaloisField 3 (3 * n))) ∧
          KFacts.InducesStdKind K c .field

end Certs


section Certs

theorem item611FieldL2Max_of_S (h : Item611FieldL2S) : Item611FieldL2Max := by
  intro G _ _ hst A hA hrank c hcA hc1 L hL hCA E hE hLE T hT hTL hTθ he hcE d hd hdc S hS hS1
    hSc
  exact (h G hst A hA hrank c hcA hc1 L hL hCA E hE hLE T hT hTL hTθ he hcE d hd hdc S hS hS1
    hSc).elim

end Certs

end CFSG.RankThree.PartTwo.Sec6
