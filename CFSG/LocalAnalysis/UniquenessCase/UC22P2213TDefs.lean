module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_8P (D : Data G) (Ch : Choice2011 G) : Prop :=
  CFSG.Open.evenRank G = 3 → H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ n : ℕ, Odd n →
    IsSp4 (Bar2 L) n → ∀ p ∈ D.sig, (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]

@[expose] def S21_17J (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, (conjSetOf D.M L).ncard = 2 → IsJ1 (Bar2 L) →
    c.n = 3 → ∀ p ∈ D.sig, p ∣ Nat.card L

@[expose] def R8100T (D : Data G) : Prop :=
  CFSG.Open.evenRank G = 3 → ∀ K ∈ calC D.M, (conjSetOf D.M K).ncard = 2 → ∀ n : ℕ, 2 < n →
    IsPowTwo n → IsL2 (Bar2 K) n → ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M →
      ∀ p ∈ D.sig, (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]

end CFSG.LocalAnalysis.UniquenessCase.UC22
