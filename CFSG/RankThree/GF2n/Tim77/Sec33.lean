module

public import CFSG.RankThree.GF2n.Tim77.Sec33Inner
public import CFSG.RankThree.GF2n.Tim77.SecYXN

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

section Certified4


theorem tim77Sec33_holds : Tim77Sec33Statement := by
  intro G _ _ A Abar S₀ B s h hs hq
  by_cases heq : conjSubgroup s Abar = Abar
  · unfold Section3.Y Section3.X
    rw [heq]
    simp
  · exact h.Y_eq_X_of_le_sup hs (sec33_inner h hs hq heq)

end Certified4

end CFSG.RankThree.GF2n.Tim77
