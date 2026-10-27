module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Core

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

structure Config (k : Sec7Core4 G) (H : Subgroup G) : Prop where
  ne_top : H ≠ ⊤
  not_le : ¬ H ≤ k.M
  two_le_pRank : 2 ≤ CFSG.Open.pRank k.p (H ⊓ k.M)

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
