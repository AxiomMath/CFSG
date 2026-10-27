module

public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

@[expose] def Item6_5Used : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ A ∈ partTwoS G,
    ∀ L ∈ thetaComponentFamily 3 A, ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B →
      Nat.card B = 9 → B ≤ A ⊓ thetaQuotCentralizer L →
      (∀ E ∈ collectionIn (partTwoE G) (A ⊔ L), B ≤ E →
        ∃ b ∈ B, b ≠ 1 ∧ ∃ K ∈ thetaComponentsAt 3 b,
          inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {b}) ⊔
            inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {b})) < K) ∧
      ((∀ E ∈ collectionIn (partTwoE G) (A ⊔ L), ¬ B ≤ E) →
        3 < CFSG.Open.pRank 3 A ∧ ∃ b ∈ B, b ≠ 1 ∧ ∃ K ∈ thetaComponentsAt 3 b,
          inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {b}) ⊔
            inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {b})) < K)

end CFSG.RankThree.PartTwo.Sec6
