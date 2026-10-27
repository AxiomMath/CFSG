module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest5
import CFSG.LocalAnalysis.UniquenessCase.UC22S213SporTwo
import CFSG.LocalAnalysis.UniquenessCase.UC22P21d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_3ClosedSpor (M L : Subgroup G) : Prop :=
  (IsSpor (BarInf L) .M12 ∨ IsSpor (BarInf L) .M24 ∨ IsSpor (BarInf L) .Ru ∨
    IsSpor (BarInf L) .J4) ∧ CFSG.Open.pRank 3 M ≤ 2

@[expose] def S21_3Rest6 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ S21_3Closed L → ¬ S21_3Closed2 L →
    ¬ S21_3ClosedZ L → ¬ S21_3ClosedCov D.M L → ¬ S21_3ClosedSpor D.M L → ¬ F08.Thin8 L →
    CFSG.Open.pRank 3 L ≤ 2 → (IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 L ≤ 1) →
    ∀ a ∈ c.B, (orderOf a).Prime →
      (∀ p ∈ D.sig,
        CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ D.M) ≤ 1) →
      ¬ CentralizesBar a L

theorem s21_3Rest5_of_rest6 (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hσ : S.InMSigma) (hSE : StronglyEmbeddedFive)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hrank : ∀ (X : Type) [Group X] [Finite X] [Nontrivial X] (s : TauCeti.SporadicName),
      s ≠ .J1 → IsSpor X s → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X))
    (hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
      ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2)
    (hSC : PartTwo.Inputs1719.K_SporadicCoverCenterOdd)
    (Ch : Choice2011 G) (h : S21_3Rest6 (UC6.dataOfSetup4 hS hU S) Ch) :
    S21_3Rest5 (UC6.dataOfSetup4 hS hU S) Ch := by
  intro hH c L hL hC hC2 hCZ hCov hthin h3 hk1 a ha hpr hN
  by_cases hSp : S21_3ClosedSpor (UC6.dataOfSetup4 hS hU S).M L
  · exact uc22s213_not_centralizesBar_of_spor hS hU S hσ hSE hOut hrank hout hSC hL hSp.1 hSp.2
      h3 hk1 (uc22p21d_odd_orderOf_of_mem_calB1 c.hB ha) hpr (hN S.p S.hp)
  · exact h hH c L hL hC hC2 hCZ hCov hSp hthin h3 hk1 a ha hpr hN

end CFSG.LocalAnalysis.UniquenessCase.UC22
