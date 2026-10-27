module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KM4
public import CFSG.RankThree.PartTwo.Sec12.Hering129KM5

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo


theorem kf_l3_pgl : KF_L3_PGL := by
  intro π p f K _ hK hq y hyH hyZ hy3 m₀ hm₀L hm₀1 hm₀3 _ Xm hXL hXc hXp hXns hm₀X
  obtain ⟨τ, hτ, hτ1, g, hg, hm₀g, e, a, b, c, he3, he1, hshape, hy⟩ :=
    exists_frame hK hq hyH hyZ hy3 hm₀L hm₀1 hm₀3 hXL hXc hXp hXns hm₀X
  subst hm₀g
  exact ⟨_, pglHess_of_frame hK hq hτ hτ1 hg he3 he1 hshape hy⟩

end CFSG.RankThree.PartTwo.Sec12
