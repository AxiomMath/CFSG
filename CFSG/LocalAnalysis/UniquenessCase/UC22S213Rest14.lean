module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest13
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213U54

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_3Rest14 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ S21_3Closed L → ¬ S21_3Closed2 L →
    ¬ S21_3ClosedZ L → ¬ S21_3ClosedCov D.M L → ¬ S21_3ClosedSpor D.M L →
    ¬ S21_3ClosedL2 L → ¬ S21_3ClosedTorus L → ¬ S21_3ClosedSmall D.M L → S21_3List L →
    (¬ D.M ≤ normalizer (L : Set G) → ∀ q : ℕ, q.Prime → q ≠ 2 →
      2 ≤ CFSG.Open.pRank q L → q ∣ Nat.card (center (Bar2 L))) →
    ¬ S21_3ClosedU3 L → ¬ S21_3ClosedTorusL3 L → ¬ S21_3ClosedTorus4 L →
    ¬ S21_3ClosedChar D.M L → ¬ S21_3ClosedU54 L → ¬ F08.Thin8 L → CFSG.Open.pRank 3 L ≤ 2 →
    (IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 L ≤ 1) →
    ∀ a ∈ c.B, (orderOf a).Prime →
      (∀ p ∈ D.sig,
        CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ D.M) ≤ 1) →
      ¬ CentralizesBar a L

theorem s21_3Rest13_of_rest14 (hgr : GriessAllModelsStatement) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M)
    (hSE : StronglyEmbeddedFive) (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (Ch : Choice2011 G) (h : S21_3Rest14 (UC6.dataOfSetup4 hS hU S) Ch) :
    S21_3Rest13 (UC6.dataOfSetup4 hS hU S) Ch := by
  intro hH c L hL hC hC2 hCZ hCov hSp hL2 hT hs hlist hnn hU3 hTL hT4 hCh hthin h3 hk1 a ha hpr hN
  by_cases hU54 : S21_3ClosedU54 L
  · exact uc22s213_not_centralizesBar_of_u54 hgr hS hU S hσ hPart hSE hOut Ch c hL hU54 hk1 ha hpr
      hN
  exact h hH c L hL hC hC2 hCZ hCov hSp hL2 hT hs hlist hnn hU3 hTL hT4 hCh hU54 hthin h3 hk1 a ha
    hpr hN

end CFSG.LocalAnalysis.UniquenessCase.UC22
