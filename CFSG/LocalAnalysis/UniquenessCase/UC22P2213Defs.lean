module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_21E (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, Hyp2120 D c → CFSG.Open.evenRank G = 3

@[expose] def S21_8E (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ n : ℕ, Odd n → IsSp4 (Bar2 L) n →
    ∀ p ∈ D.sig, CFSG.Open.pRank p D.M ≤ 3

@[expose] def R8100E (D : Data G) : Prop :=
  3 < CFSG.Open.evenRank G → ∀ K ∈ calC D.M, (conjSetOf D.M K).ncard = 2 →
    ∀ n : ℕ, 2 ≤ n → IsPowTwo n → IsL2 (Bar2 K) n →
      CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M

end CFSG.LocalAnalysis.UniquenessCase.UC22
