module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_21EB (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, c.B ≠ ⊥ → Hyp2120 D c → CFSG.Open.evenRank G = 3

end CFSG.LocalAnalysis.UniquenessCase.UC22
