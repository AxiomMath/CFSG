module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148MK425Lie
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT2Nine
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT2Eight
public import CFSG.RankThree.PartTwo.Sec4.Ronan148HRow425L67
public import CFSG.RankThree.PartTwo.Sec4.Ronan148HRow425L3U3
public import CFSG.RankThree.PartTwo.Sec4.Ronan148HRow425U4
public import CFSG.RankThree.PartTwo.Sec4.Ronan148HRow425D4
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Rows
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1F42
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1U62
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Tits
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1L52
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Om8
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1O8p
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1U52
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1U58
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1D42
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1U44
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1L264
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1U3
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LH1Gen424Rows
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LH1E27Rows
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LH1Syl9
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT2SU4
public import CFSG.RankThree.PartTwo.Sec4.Ronan148HRow425F4
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1L3Even
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT2L3Rows
public import CFSG.RankThree.PartTwo.Sec4.Ronan148HRow425G2p
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1G24
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LL34Row

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)

structure K425OpenRowsLie2 : Prop where
  two_SL : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 →
    RowOf425 (projSL 3 (GaloisField p e))
  two_SU : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 → RowOf425 (projSU 3 p e)
  four_G2 : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ q : TauCeti.PrimePower, q.p = p → q.exponent = 1 →
    ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid, RowOf425 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group

structure K427OpenRows : Prop where
  seven_SL3 : RowOf427 (projSL 3 (GaloisField 2 2))
section K425


theorem K425OpenRowsLie2.toLie (h : K425OpenRowsLie2) : K425OpenRowsLie where
  two_SL := h.two_SL
  two_SU := h.two_SU
  four_G2 := h.four_G2
  four_Sp := Ronan148L.kT2_four_Sp
  four_SL := Ronan148L.kT2_four_SL
  four_SU := Ronan148L.kT2_four_SU
  seven_SL3 := Sec4.Ronan148H.rowOf425_projSL_three_two
  seven_SU3 := Sec4.Ronan148H.rowOf425_projSU_three_two
  seven_Sp4 := Ronan148L.kT2_seven_Sp4
  seven_SU4 := Sec4.Ronan148H.rowOf425_projSU_four_two
  seven_G2 := Sec4.Ronan148H.rowOf425_g2
  seven_D4 := Sec4.Ronan148H.rowOf425_d4
  seven_F4 := Sec4.Ronan148H.rowOf425_reeF4
  eight_SL6 := Sec4.Ronan148H.k425_eight_SL6
  eight_SL7 := Sec4.Ronan148H.k425_eight_SL7
  eight_SL4 := Ronan148L.kT2_eight_SL4
  eight_Sp6_4 := Ronan148L.kT2_eight_Sp6_4
  eight_SU5_8 := Ronan148L.kT2_eight_SU5_8
  seven_Tits := Ronan148L.kT2_seven_Tits
  eight_SU6 := Ronan148L.kT2_eight_SU6
  eight_Sp6 := Ronan148L.kT2_eight_Sp6
  eight_OmegaPlus := Ronan148L.kT2_eight_OmegaPlus
  eight_Sp8 := Ronan148L.kT2_eight_Sp8
  eight_OmegaMinus := Ronan148L.kT2_eight_OmegaMinus
  eight_F4 := Ronan148L.kT2_eight_F4
  eight_SU5 := Ronan148L.kT2_eight_SU5
  nine_SL3_nine := Ronan148L.kT2_nine_SL3_nine
  nine_SU3_nine := Ronan148L.kT2_nine_SU3_nine
  nine_SL4 := Ronan148L.kT2_nine_SL4

theorem k425OpenRowsLie2_holds : K425OpenRowsLie2 :=
  ⟨Ronan148L.kT2_two_SL, Ronan148L.kT2_two_SU, Sec4.Ronan148H.rowOf425_g2_prime⟩

end K425

section K427


theorem K427OpenRows.toRows
    (h : K427OpenRows) : K427Rows where
  one := by
    intro p e _ hp2 he
    by_cases h5 : p = 5
    · exact Ronan148L.kH1_one_ge_five p e (by omega) he
    · by_cases h3 : p = 3 ∧ e ≤ 2
      · obtain ⟨rfl, he2⟩ := h3
        rcases Nat.lt_or_ge e 2 with h1 | h2
        · obtain rfl : e = 1 := by omega
          exact Ronan148L.kH1_one_three_one
        · obtain rfl : e = 2 := by omega
          exact Ronan148L.kH1_one_three_two
      · exact Ronan148L.kH1_one_of p e hp2 he h5 h3
  two_SL := by
    intro p e _ hp he he2
    by_cases h5 : p = 5
    · subst h5
      rcases Nat.lt_or_ge e 2 with h1 | h2
      · obtain rfl : e = 1 := by omega
        exact Ronan148L.kH1_two_SL_five
      · obtain rfl : e = 2 := by omega
        exact Ronan148L.kH1_two_SL_five_two
    · exact Ronan148L.kH1_two_SL_of_ne_five p e hp he he2 h5
  two_SU := by
    intro p e _ hp he he2
    by_cases h5 : p = 5
    · subst h5
      rcases Nat.lt_or_ge e 2 with h1 | h2
      · obtain rfl : e = 1 := by omega
        exact Ronan148L.kH1_two_SU_five
      · obtain rfl : e = 2 := by omega
        exact Ronan148L.kH1_two_SU_five_two
    · exact Ronan148L.kH1_two_SU_of_ne_five p e hp he he2 h5
  three := Ronan148L.kH1_three
  four_G2 := by
    intro p _ hp q hqp hqe hq
    by_cases h5 : p = 5
    · subst h5; exact Ronan148L.kH1_four_G2_five q hqp hqe hq
    · exact Ronan148L.kH1_four_G2_of_ne_five p hp q hqp hqe hq h5
  four_Sp := by
    intro p _ hp
    by_cases h5 : p = 5
    · subst h5; exact Ronan148L.kH1_four_Sp_five
    · exact Ronan148L.kH1_four_Sp_of_ne_five p hp h5
  four_SL := by
    intro p _ hp
    by_cases h5 : p = 5
    · subst h5; exact Ronan148L.kH1_four_SL_five
    · exact Ronan148L.kH1_four_SL_of_ne_five p hp h5
  four_SU := by
    intro p _ hp
    by_cases h5 : p = 5
    · subst h5; exact Ronan148L.kH1_four_SU_five
    · exact Ronan148L.kH1_four_SU_of_ne_five p hp h5
  five := Ronan148R.k427Five
  six := Ronan148R.k427Six
  seven_SL2 := Ronan148R.rowOf427_sl2
  seven_SL3 := by
    intro n hn
    rcases Nat.even_or_odd n with he | ho
    · by_cases h2 : n = 2
      · subst h2; exact h.seven_SL3
      · exact Ronan148R.rowOf427_sl3_even n (by obtain ⟨k, hk⟩ := he; omega) he
    · exact Ronan148R.rowOf427_sl3_odd n ho
  seven_SU3 := by
    intro n hn
    rcases Nat.even_or_odd n with he | ho
    · exact Ronan148R.rowOf427_su3_even n hn he
    · exact Ronan148R.rowOf427_su3_odd n hn ho
  seven_Sp4 := Ronan148R.rowOf427_sp4
  seven_SU4 := by
    intro n hn
    by_cases h2 : n = 2
    · subst h2; exact Ronan148R.rowOf427_su44
    · exact Ronan148R.rowOf427_su4 n hn h2
  seven_G2 := by
    intro q hq2 hq
    rcases Nat.even_or_odd q.exponent with he | ho
    · by_cases h2 : q.exponent = 2
      · exact Ronan148R.rowOf427_g2_four q hq2 h2 hq
      · exact Ronan148R.rowOf427_g2_even q hq2 he
          (by obtain ⟨k, hk⟩ := he; have := q.exponent_pos; omega) hq
    · exact Ronan148R.rowOf427_g2_odd q hq2 ho hq
  seven_D4 := by
    intro q hq hq2
    by_cases he : q.exponent = 1
    · exact Ronan148R.rowOf427_d42 q hq hq2 he
    · exact Ronan148R.rowOf427_d4 q hq hq2 he
  seven_Tits := Ronan148R.rowOf427_tits
  eight_SL5 := Ronan148R.rowOf427_l52
  eight_SU5 := Ronan148R.rowOf427_su52
  eight_SL6 := Ronan148R.rowOf427_l62
  eight_SU6 := Ronan148R.rowOf427_u62
  eight_SL7 := Ronan148R.rowOf427_l72
  eight_Sp6 := Ronan148R.rowOf427_sp6
  eight_Sp8 := Ronan148R.rowOf427_sp8
  eight_OmegaPlus := Ronan148R.rowOf427_o8p
  eight_OmegaMinus := Ronan148R.rowOf427_om8
  eight_SL4 := Ronan148L.kH1_eight_SL4
  eight_Sp6_4 := Ronan148L.kH1_eight_Sp6_4
  eight_SU5_4 := Ronan148R.rowOf427_su54
  eight_SU5_8 := Ronan148R.rowOf427_su58
  eight_F4 := Ronan148R.rowOf427_f42
  seven_Sz := Ronan148L.kH1_seven_Sz
  seven_F4 := Ronan148L.kH1_seven_F4
  nine_SL3 := Ronan148L.kH1_nine_SL3
  nine_SU3 := Ronan148L.kH1_nine_SU3
  nine_G2 := Ronan148L.kH1_nine_G2
  nine_SL4 := Ronan148L.kH1_nine_SL4
  nine_SU4 := Ronan148L.kH1_nine_SU4

theorem k427OpenRows_holds
    : K427OpenRows := ⟨Ronan148L.rowOf427_L34⟩

end K427

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
