module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

@[expose] def UniqueMaxL0T (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx22b D Ch, ∃ N : Subgroup G, D.T ≤ N ∧ N < c.L0 ⊔ D.T ∧
    ∀ Y : Subgroup G, D.T ≤ Y → Y < c.L0 ⊔ D.T → Y ≤ N

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
