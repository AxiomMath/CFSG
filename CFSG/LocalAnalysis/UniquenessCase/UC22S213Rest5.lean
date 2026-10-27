module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest4
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Cov
import CFSG.LocalAnalysis.UniquenessCase.UC22P21d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_3ClosedCov (M L : Subgroup G) : Prop :=
  (F08.IsA6Z3 (Bar2 L) ∨ F08.IsA7Z3 (Bar2 L) ∨ F08.IsM22Z3 (Bar2 L)) ∧
    CFSG.Open.pRank 3 M ≤ 2

@[expose] def S21_3Rest5 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ S21_3Closed L → ¬ S21_3Closed2 L →
    ¬ S21_3ClosedZ L → ¬ S21_3ClosedCov D.M L → ¬ F08.Thin8 L → CFSG.Open.pRank 3 L ≤ 2 →
    (IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 L ≤ 1) →
    ∀ a ∈ c.B, (orderOf a).Prime →
      (∀ p ∈ D.sig,
        CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ D.M) ≤ 1) →
      ¬ CentralizesBar a L

theorem s21_3Rest4_of_rest5 (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hσ : S.InMSigma) (hSE : StronglyEmbeddedFive)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
      ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2)
    (Ch : Choice2011 G) (h : S21_3Rest5 (UC6.dataOfSetup4 hS hU S) Ch) :
    S21_3Rest4 (UC6.dataOfSetup4 hS hU S) Ch := by
  intro hH c L hL hC hC2 hCZ hthin h3 hk1 a ha hpr hN
  by_cases hCov : S21_3ClosedCov (UC6.dataOfSetup4 hS hU S).M L
  · exact uc22s213_not_centralizesBar_of_cover hS hU S hσ hSE hOut hout hL hCov.1 hCov.2 hk1
      (uc22p21d_odd_orderOf_of_mem_calB1 c.hB ha) hpr (hN S.p S.hp)
  · exact h hH c L hL hC hC2 hCZ hCov hthin h3 hk1 a ha hpr hN

end CFSG.LocalAnalysis.UniquenessCase.UC22
