module

public import CFSG.RankThree.GF2n.Stroth80.Sec7WVSecCard
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmts

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank


theorem sec7WVMinOrder_of (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (h52a : Stroth52aStatement) (h52b : Stroth52bStatement) : Sec7WVMinOrderStatement := by
  intro G _ _ M Q Z B hc n t hs A hVA hAW hAR hAne m hm2
  have hcard := sec7WVSecCard_of hA hPts h52a h52b G M Q Z B hc n t hs A hVA hAW hAR m hm2
  have hq : 1 < Nat.card Z := by
    have := hc.hyp.q4
    omega
  have hVP : Vt M (LB M Q B) B Z t < A := lt_of_le_of_ne hVA (Ne.symm hAne)
  refine ⟨fun hMinus => ?_, fun hPlus hm3 => ?_⟩
  · obtain ⟨k, hk⟩ := hcard.1 hMinus
    exact sec7_secOrder_ge hVP hq Nat.one_le_two_pow hk
  · obtain ⟨k, hk⟩ := hcard.2 hPlus hm3
    exact sec7_secOrder_ge hVP hq Nat.one_le_two_pow hk

end CFSG.RankThree.GF2n.Stroth80
