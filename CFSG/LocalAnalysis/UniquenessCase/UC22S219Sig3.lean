module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_9Sig3 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal →
    ∀ n : ℕ, IsSU3 (Bar2 L) n → ¬ IsPowTwo n → CFSG.Open.evenRank G = 3 →
      Odd n ∧ 3 ∈ D.sig

end CFSG.LocalAnalysis.UniquenessCase.UC22
