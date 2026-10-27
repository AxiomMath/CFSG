module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest8
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22S213NotNormal
import CFSG.LocalAnalysis.UniquenessCase.UC22P21d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_3Rest9 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ S21_3Closed L → ¬ S21_3Closed2 L →
    ¬ S21_3ClosedZ L → ¬ S21_3ClosedCov D.M L → ¬ S21_3ClosedSpor D.M L →
    ¬ S21_3ClosedL2 L → ¬ S21_3ClosedTorus L → ¬ S21_3ClosedSmall D.M L → S21_3List L →
    (¬ D.M ≤ normalizer (L : Set G) → ∀ q : ℕ, q.Prime → q ≠ 2 →
      2 ≤ CFSG.Open.pRank q L → q ∣ Nat.card (center (Bar2 L))) →
    ¬ F08.Thin8 L → CFSG.Open.pRank 3 L ≤ 2 →
    (IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 L ≤ 1) →
    ∀ a ∈ c.B, (orderOf a).Prime →
      (∀ p ∈ D.sig,
        CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ D.M) ≤ 1) →
      ¬ CentralizesBar a L

theorem s21_3Rest8_of_rest9 {D : Data G} {Ch : Choice2011 G} (hσ : UC6S846.SigmaStd D)
    (h : S21_3Rest9 D Ch) : S21_3Rest8 D Ch := by
  intro hH c L hL hC hC2 hCZ hCov hSp hL2 hT hs hlist hthin h3 hk1 a ha hpr hN haL
  exact h hH c L hL hC hC2 hCZ hCov hSp hL2 hT hs hlist
    (fun hMN _ hq hq2 h2 => uc22s213_dvd_card_center_of_not_normal hσ hL hMN
      (uc22p21d_odd_orderOf_of_mem_calB1 c.hB ha) hpr haL hN hq hq2 h2)
    hthin h3 hk1 a ha hpr hN haL

end CFSG.LocalAnalysis.UniquenessCase.UC22
