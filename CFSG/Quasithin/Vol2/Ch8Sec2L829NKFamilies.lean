module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKL3In
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKU3In
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKOutFam
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKL2In
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKL2Out
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKL3OddIn
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKL3Out
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKU3OddIn
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKU3Out

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13

theorem nk_leafL3TwoOdd : NKLeafL3TwoOdd := by
  intro n hn h3 X _ hX
  exact ⟨nk_l3_uin n hn h3 X hX, nk_l3_out n (by omega) X hX⟩

theorem nk_leafU3Even : NKLeafU3Even := by
  intro n hn X _ hX
  have h1 : 1 ≤ n := hX.1.2.1
  exact ⟨nk_u3_uin n (by omega) hn X hX, nk_u3_out n (by omega) X hX⟩

theorem nk_leafL2Odd : NKLeafL2Odd := by
  intro p e hp h3 he h8 h7 h25 X _ hX
  exact ⟨nk_l2_uin p e hp h3 he h8 h7 h25 X hX, nk_l2_out p e hp h3 he h8 h7 h25 X hX⟩

theorem nk_leafL3Odd : NKLeafL3Odd := by
  intro p hp h7 h4 X _ hX
  exact ⟨nk_l3odd_uin p hp h7 h4 X hX, nk_l3odd_out p hp h7 h4 X hX⟩

theorem nk_leafU3Odd : NKLeafU3Odd := by
  intro p hp h13 h4 X _ hX
  exact ⟨nk_u3odd_uin p hp h13 h4 X hX, U3Out.nk_u3odd_out p hp h13 h4 X hX⟩

end CFSG.Quasithin.H13.L829NK
