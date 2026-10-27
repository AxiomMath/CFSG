module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest6
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213L2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_3Rest7 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ S21_3Closed L → ¬ S21_3Closed2 L →
    ¬ S21_3ClosedZ L → ¬ S21_3ClosedCov D.M L → ¬ S21_3ClosedSpor D.M L →
    ¬ S21_3ClosedL2 L → ¬ F08.Thin8 L → CFSG.Open.pRank 3 L ≤ 2 →
    (IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 L ≤ 1) →
    ∀ a ∈ c.B, (orderOf a).Prime →
      (∀ p ∈ D.sig,
        CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ D.M) ≤ 1) →
      ¬ CentralizesBar a L

theorem s21_3Rest6_of_rest7 (hGA : GriessAllModelsStatement) {D : Data G} {Ch : Choice2011 G}
    (h : S21_3Rest7 D Ch) : S21_3Rest6 D Ch := by
  intro hH c L hL hC hC2 hCZ hCov hSp hthin h3 hk1 a ha hpr hN
  by_cases hL2 : S21_3ClosedL2 L
  · exact (uc22s213_false_of_closedL2 hGA hL hL2 hCZ hthin h3).elim
  · exact h hH c L hL hC hC2 hCZ hCov hSp hL2 hthin h3 hk1 a ha hpr hN

end CFSG.LocalAnalysis.UniquenessCase.UC22
