module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G]

@[expose] def IsLThreeTypeAt (p : ℕ) (L : Subgroup G) : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 3 2 f

end CFSG.RankThree.PartOne
