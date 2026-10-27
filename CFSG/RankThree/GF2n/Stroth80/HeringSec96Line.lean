module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec96Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Main

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement


theorem sec96Line_of : HS9.Sec96LineStatement := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit
  have ht : t ∈ LB M Q B := hs.mem
  obtain ⟨⟨-, -, -, hYR, -, -, -⟩, -, -⟩ := hsplit
  refine sup_le sec39_Z_le_Vt (iSup₂_le fun y hy => ?_)
  exact le_sup_left.trans (hc.conj_Rt_le_Vt ht (hYR hy))

end CFSG.RankThree.GF2n.Stroth80
