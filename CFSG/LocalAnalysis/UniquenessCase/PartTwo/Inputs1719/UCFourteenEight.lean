module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def R14_8 (D : Data G) : Prop :=
  ∀ L ∈ calC D.M, (conjSetOf D.M L).ncard = 2 →
    (∃ n : ℕ, IsSz (Bar2 L) n) → CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.eM D.M ≤ 3 →
      UniqueMax D.M L

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
