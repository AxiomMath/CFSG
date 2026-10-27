module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest15Reduction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def Rest15Norm (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ S21_3Closed L → ¬ S21_3Closed2 L →
    ¬ S21_3ClosedZ L → ¬ S21_3ClosedCov D.M L → ¬ S21_3ClosedSpor D.M L →
    ¬ S21_3ClosedL2 L → ¬ S21_3ClosedTorus L → ¬ S21_3ClosedSmall D.M L → S21_3List L →
    (¬ D.M ≤ normalizer (L : Set G) → ∀ q : ℕ, q.Prime → q ≠ 2 →
      2 ≤ CFSG.Open.pRank q L → q ∣ Nat.card (center (Bar2 L))) →
    ¬ S21_3ClosedU3 L → ¬ S21_3ClosedTorusL3 L → ¬ S21_3ClosedTorus4 L →
    ¬ S21_3ClosedChar D.M L → ¬ S21_3ClosedU54 L → ¬ S21_3ClosedCharY D.M L →
    ¬ F08.Thin8 L → CFSG.Open.pRank 3 L ≤ 2 →
    (IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 L ≤ 1) →
    (D.M ≤ normalizer (L : Set G)) →
    ∀ a ∈ c.B, (orderOf a).Prime →
      (∀ p ∈ D.sig,
        CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ D.M) ≤ 1) →
      ¬ CentralizesBar a L

@[expose] def Rest15Covers (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ S21_3Closed L → ¬ S21_3Closed2 L →
    ¬ S21_3ClosedZ L → ¬ S21_3ClosedCov D.M L → ¬ S21_3ClosedSpor D.M L →
    ¬ S21_3ClosedL2 L → ¬ S21_3ClosedTorus L → ¬ S21_3ClosedSmall D.M L → S21_3List L →
    (¬ D.M ≤ normalizer (L : Set G) → ∀ q : ℕ, q.Prime → q ≠ 2 →
      2 ≤ CFSG.Open.pRank q L → q ∣ Nat.card (center (Bar2 L))) →
    ¬ S21_3ClosedU3 L → ¬ S21_3ClosedTorusL3 L → ¬ S21_3ClosedTorus4 L →
    ¬ S21_3ClosedChar D.M L → ¬ S21_3ClosedU54 L → ¬ S21_3ClosedCharY D.M L →
    ¬ F08.Thin8 L → CFSG.Open.pRank 3 L ≤ 2 →
    (IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 L ≤ 1) →
    ¬ D.M ≤ normalizer (L : Set G) → FiveCovers (Bar2 L) →
    ∀ a ∈ c.B, (orderOf a).Prime →
      (∀ p ∈ D.sig,
        CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ D.M) ≤ 1) →
      ¬ CentralizesBar a L

@[expose] def Rest15Center (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ S21_3Closed L → ¬ S21_3Closed2 L →
    ¬ S21_3ClosedZ L → ¬ S21_3ClosedCov D.M L → ¬ S21_3ClosedSpor D.M L →
    ¬ S21_3ClosedL2 L → ¬ S21_3ClosedTorus L → ¬ S21_3ClosedSmall D.M L → S21_3List L →
    (¬ D.M ≤ normalizer (L : Set G) → ∀ q : ℕ, q.Prime → q ≠ 2 →
      2 ≤ CFSG.Open.pRank q L → q ∣ Nat.card (center (Bar2 L))) →
    ¬ S21_3ClosedU3 L → ¬ S21_3ClosedTorusL3 L → ¬ S21_3ClosedTorus4 L →
    ¬ S21_3ClosedChar D.M L → ¬ S21_3ClosedU54 L → ¬ S21_3ClosedCharY D.M L →
    ¬ F08.Thin8 L → CFSG.Open.pRank 3 L ≤ 2 →
    (IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 L ≤ 1) →
    ¬ D.M ≤ normalizer (L : Set G) → ¬ FiveCovers (Bar2 L) → 3 ∣ Nat.card (center (Bar2 L)) →
    ∀ a ∈ c.B, (orderOf a).Prime →
      (∀ p ∈ D.sig,
        CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ D.M) ≤ 1) →
      ¬ CentralizesBar a L

@[expose] def Rest15ModelCase (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ S21_3Closed L → ¬ S21_3Closed2 L →
    ¬ S21_3ClosedZ L → ¬ S21_3ClosedCov D.M L → ¬ S21_3ClosedSpor D.M L →
    ¬ S21_3ClosedL2 L → ¬ S21_3ClosedTorus L → ¬ S21_3ClosedSmall D.M L → S21_3List L →
    (¬ D.M ≤ normalizer (L : Set G) → ∀ q : ℕ, q.Prime → q ≠ 2 →
      2 ≤ CFSG.Open.pRank q L → q ∣ Nat.card (center (Bar2 L))) →
    ¬ S21_3ClosedU3 L → ¬ S21_3ClosedTorusL3 L → ¬ S21_3ClosedTorus4 L →
    ¬ S21_3ClosedChar D.M L → ¬ S21_3ClosedU54 L → ¬ S21_3ClosedCharY D.M L →
    ¬ F08.Thin8 L → CFSG.Open.pRank 3 L ≤ 2 →
    (IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 L ≤ 1) →
    ¬ D.M ≤ normalizer (L : Set G) → ¬ FiveCovers (Bar2 L) → ¬ 3 ∣ Nat.card (center (Bar2 L)) → Rest15Models D.M L →
    ∀ a ∈ c.B, (orderOf a).Prime →
      (∀ p ∈ D.sig,
        CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ D.M) ≤ 1) →
      ¬ CentralizesBar a L

end CFSG.LocalAnalysis.UniquenessCase.UC22
