module

public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

@[expose] def Item6_4_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoE G,
    (fourGroups A).Nonempty

@[expose] def Item6_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    ∀ L ∈ thetaComponentFamily 3 A, ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B →
      Nat.card B = 9 → B ≤ A ⊓ thetaQuotCentralizer L →
      (∀ E ∈ collectionIn (partTwoE G) (A ⊔ L), B ≤ E →
        ∃ b ∈ B, b ≠ 1 ∧ ∃ K ∈ thetaComponentsAt 3 b,
          inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {b}) ⊔
            inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {b})) < K ∧
          ∃ S ∈ invariantPiSubgroups K E (piOf 2), S ≠ ⊥ ∧ ⁅S, B⁆ = S) ∧
      ((∀ E ∈ collectionIn (partTwoE G) (A ⊔ L), ¬ B ≤ E) →
        3 < CFSG.Open.pRank 3 A ∧ ∃ b ∈ B, b ≠ 1 ∧ ∃ K ∈ thetaComponentsAt 3 b,
          inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {b}) ⊔
            inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {b})) < K)

@[expose] def Item6_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G, ∀ L ∈ lStar A,
    IsCyclic (A ⊓ thetaQuotCentralizer L : Subgroup G)

@[expose] def Item6_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    ∀ E ∈ collectionIn (partTwoE G) A, ∀ L ∈ lStarOf A E, ∀ T ∈ fourGroupsPlus E,
      T ≤ Subgroup.normalizer (L : Set G)

@[expose] def Item6_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    ∀ E ∈ collectionIn (partTwoE G) A, ∀ T ∈ fourGroupsPlus E, ∀ B : Subgroup G, B ≤ E →
      CFSG.Assembly.IsElemAbelian 3 B → Nat.card B = 9 →
      ∃ b ∈ B, b ≠ 1 ∧ ∃ L ∈ lZeroAt A b,
        ¬ ⁅L, T⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L

@[expose] def Item6_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    ∀ E ∈ collectionIn (partTwoE G) A, (lZero E).Nonempty

@[expose] def Item6_11_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoF G,
    CFSG.Open.pRank 3 A ≤ 4

@[expose] def Item6_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    ∀ E ∈ collectionIn (partTwoE G) A, ∀ U ∈ fourGroups E,
      ∃ c ∈ E, c ≠ 1 ∧ ∃ L ∈ lZeroStarAt A c,
        U ≤ Subgroup.normalizer (L : Set G) ∧ ⁅L, U⁆ = L ∧
        ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓ Subgroup.centralizer {c},
            E ⊓ Subgroup.centralizer (U : Set G)⁆ ≤ Subgroup.normalizer (L : Set G) ∧
        ⁅L, ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ⊓
            Subgroup.centralizer {c}, E ⊓ Subgroup.centralizer (U : Set G)⁆⁆ = L

end CFSG.RankThree.PartTwo.Sec6
