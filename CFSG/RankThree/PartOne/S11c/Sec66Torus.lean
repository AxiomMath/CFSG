module

public import CFSG.RankThree.PartOne.S11c.Sec66TDefs

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)

@[expose] def PSLTorusRank : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (n f p : ℕ), p.Prime → 5 ≤ p → p ∣ n → p ∣ 2 ^ f - 1 →
    StatedClassicalModel T .PSL n 2 f → ¬ LocalRankLeTwo p T

end CFSG.RankThree.PartOne.Sec66T
