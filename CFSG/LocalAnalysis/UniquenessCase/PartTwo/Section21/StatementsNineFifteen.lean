module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

section Section21

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_9TorusN (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal →
    ∀ n : ℕ, IsSU3 (Bar2 L) n → ∀ s : ℕ, Odd s → s ∣ n → ∀ r : ℕ, r.Prime → r ∣ 2 ^ s - 1 →
      ∃ X : Subgroup G, Nat.card X = r ∧ X ≤ L ∧ X ≤ normalizer (D.T : Set G)

@[expose] def S21_9NFull (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal →
    ∀ n : ℕ, IsSU3 (Bar2 L) n → ¬ IsPowTwo n →
      (n % 6 = 1 ∨ n % 6 = 5) ∧ (D.sig = {3} ∧ CFSG.Open.evenRank G = 3) ∧
        ∀ q : ℕ, q.Prime → 3 < q → q ∣ 2 ^ n + 1 →
          CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M

@[expose] def S21_15Torus (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ n : ℕ, (IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) →
    conjClosure D.M L ≠ L → ∀ s : ℕ, Odd s → s ∣ n → ∀ r : ℕ, r.Prime → r ∣ 2 ^ s - 1 →
      ∃ X : Subgroup G, Nat.card X = r ∧ X ≤ D.M ∧ X ≤ normalizer (D.T : Set G)

@[expose] def S21_15Rank (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ n : ℕ, (IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) →
    ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ n - 1 →
      (conjSetOf D.M L).ncard ≤ CFSG.Open.pRank r D.M

end Section21

end CFSG.LocalAnalysis.UniquenessCase.UC22
