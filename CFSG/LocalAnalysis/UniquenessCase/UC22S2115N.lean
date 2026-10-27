module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_15N (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ n : ℕ, (IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) →
    conjClosure D.M L ≠ L → ∀ s : ℕ, Odd s → s ∣ n → ∀ r : ℕ, r.Prime → r ∣ 2 ^ s - 1 →
      ∀ p ∈ D.sig, ∀ A : Subgroup G, Nat.card A = r → A ≤ L →
        (¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M ∧ A ∈ uniqueSet D.M) ∧
        (conjSetOf D.M L).ncard = 2 ∧
        ((CFSG.Open.evenRank G = 3 ∧
            ((IsL2 (Bar2 L) n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
              (IsSz (Bar2 L) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)]))) ∨
          (IsL2 (Bar2 L) 3 ∧ p = 3) ∨
          (IsSz (Bar2 L) 5 ∧ p = 5))

end CFSG.LocalAnalysis.UniquenessCase.UC22
