module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148EpsTransfer
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowOrd
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowGF4
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowSpor
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowGF2
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowL2Three
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowD4
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowF4
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowSp4
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsU4Odd
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsU3Odd
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowL4p
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowU4p

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem prime_mod_three_eq {p : ℕ} (hp : p.Prime) (h3 : 3 < p) : p % 3 = 1 ∨ p % 3 = 2 := by
  have h0 : p % 3 ≠ 0 := by
    intro h0
    rcases hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h0) with h | h <;> omega
  omega

section Rows


theorem kEpsRowsS_holds : KEpsRowsS where
  one p e _ _ he := by
    by_cases h : p = 3 ∧ 3 ≤ e
    · obtain ⟨rfl, he3⟩ := h
      exact rowSEpsOf_one_three e he3
    · exact rowSEpsOf_one p e he (by omega)
  two_SL := rowSEpsOf_two_SL
  two_SU := rowSEpsOf_two_SU
  three := rowSEpsOf_three
  four_G2 := rowSEpsOf_four_G2
  four_Sp := rowSEpsOf_four_Sp
  four_SL p _ hp := by
    rcases prime_mod_three_eq Fact.out hp with h | h
    · exact rowSEpsOf_four_SL_mod_one p hp h
    · exact rowSEpsOf_four_SL_of_mod_two p hp h
  four_SU p _ hp := by
    rcases prime_mod_three_eq Fact.out hp with h | h
    · exact rowSEpsOf_four_SU_of_mod_one p hp h
    · exact rowSEpsOf_four_SU_mod_two p hp h
  five n h5 h12 := by
    rcases (show n ≤ 8 ∨ 9 ≤ n by omega) with h | h
    · exact rowSEpsOf_alternating_le_eight h5 h
    · exact rowSEpsOf_alternating_nine_twelve h h12
  six s hs := by
    simp only [sporadics42, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [rowSEpsOf_m11, rowSEpsOf_m12, rowSEpsOf_m22, rowSEpsOf_m23, rowSEpsOf_m24,
      rowSEpsOf_j1, rowSEpsOf_j2, rowSEpsOf_j3, rowSEpsOf_j4, rowSEpsOf_mcl,
      rowSEpsOf_ly, rowSEpsOf_hs, rowSEpsOf_he, rowSEpsOf_suz, rowSEpsOf_ru,
      rowSEpsOf_on, rowSEpsOf_co3, rowSEpsOf_co2, rowSEpsOf_hn, rowSEpsOf_th]
  seven_SL2 := rowSEpsOf_seven_SL2
  seven_SL3 := rowSEpsOf_seven_SL3
  seven_SU3 := rowSEpsOf_seven_SU3_of u3OddInnerEps
  seven_Sp4 := rowSEpsOf_seven_Sp4
  seven_SU4 := rowSEpsOf_seven_SU4_of u4OddInnerEps
  seven_G2 := rowSEpsOf_seven_G2
  seven_D4 := rowSEpsOf_seven_D4
  seven_Sz := rowSEpsOf_seven_Sz
  seven_F4 := rowSEpsOf_seven_F4
  seven_Tits := rowSEpsOf_seven_Tits
  eight_SL5 := rowSEpsOf_eight_SL5
  eight_SU5 := rowSEpsOf_eight_SU5
  eight_SL6 := rowSEpsOf_eight_SL6
  eight_SU6 := rowSEpsOf_eight_SU6
  eight_SL7 := rowSEpsOf_eight_SL7
  eight_Sp6 := rowSEpsOf_eight_Sp6
  eight_Sp8 := rowSEpsOf_eight_Sp8
  eight_OmegaPlus := rowSEpsOf_eight_OmegaPlus
  eight_OmegaMinus := rowSEpsOf_eight_OmegaMinus
  eight_SL4 := rowSEpsOf_eight_SL4
  eight_Sp6_4 := rowSEpsOf_eight_Sp6_4
  eight_SU5_4 := rowSEpsOf_eight_SU5_4
  eight_SU5_8 := rowSEpsOf_eight_SU5_8
  eight_F4 := rowSEpsOf_eight_F4
  nine_SL3 := rowSEpsOf_nine_SL3
  nine_SU3 := rowSEpsOf_nine_SU3
  nine_G2 := rowSEpsOf_nine_G2
  nine_SL4 := rowSEpsOf_nine_SL4
  nine_SU4 := rowSEpsOf_nine_SU4

end Rows

section Outer


theorem item4_29EpsOuter_holds
    : Sec14.Item4_29EpsOuter :=
  Sec14.item4_29EpsOuter_of_rowsS kEpsRowsS_holds

end Outer

end CFSG.RankThree.PartTwo.Sec4.RonanEps
