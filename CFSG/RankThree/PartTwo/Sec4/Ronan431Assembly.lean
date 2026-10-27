module

public import CFSG.RankThree.PartTwo.Sec4.Ronan431Transfer
public import CFSG.RankThree.PartTwo.Sec4.Ronan431RowsEasy
public import CFSG.RankThree.PartTwo.Sec4.Ronan431RowsW
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan431

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

theorem mod_three_of_prime {p : ℕ} (hp : p.Prime) (h3 : 3 < p) : p % 3 = 1 ∨ p % 3 = 2 := by
  have h0 : p % 3 ≠ 0 := by
    intro h0
    rcases hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h0) with h | h <;> omega
  omega

section Rows

theorem k431RowsS_of_parts (B : K431OpenB) (C : K431OpenC) (D : K431OpenD) (W : K431OpenW) :
    K431RowsS where
  one p e _ h2 he := by
    by_cases h : p ≠ 3 ∨ e ≤ 2
    · exact rowSOf431_one p e he h
    · push Not at h
      obtain ⟨rfl, he3⟩ := h
      rcases (show e = 3 ∨ 4 ≤ e by omega) with rfl | he4
      · exact W.one_27
      · exact B.one_ge4 e he4
  two_SL := rowSOf431_two_SL
  two_SU := rowSOf431_two_SU
  three := rowSOf431_three
  four_G2 := rowSOf431_four_G2
  four_Sp := rowSOf431_four_Sp
  four_SL p _ hp := by
    rcases mod_three_of_prime (p := p) Fact.out hp with h | h
    · exact D.four_SL_mod_one p hp h
    · exact rowSOf431_four_SL_of_mod_two p hp h
  four_SU p _ hp := by
    rcases mod_three_of_prime (p := p) Fact.out hp with h | h
    · exact rowSOf431_four_SU_of_mod_one p hp h
    · exact D.four_SU_mod_two p hp h
  five n hn5 hn12 := by
    by_cases h8 : n ≤ 8
    · exact rowSOf431_alternating_le_eight hn5 h8
    · rcases (show n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 by omega) with rfl | rfl | rfl | rfl
      · exact rowSOf431_alternatingGroup_nine
      · exact D.five_ten
      · exact D.five_eleven
      · exact B.five_twelve
  six s hs := by
    simp only [sporadics42, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rowSOf431_m11
    · exact rowSOf431_m12
    · exact rowSOf431_m22
    · exact rowSOf431_m23
    · exact rowSOf431_m24
    · exact rowSOf431_j1
    · exact rowSOf431_j2
    · exact rowSOf431_j3
    · exact rowSOf431_j4
    · exact B.six_McL
    · exact B.six_Ly
    · exact rowSOf431_hs
    · exact rowSOf431_he
    · exact B.six_Suz
    · exact rowSOf431_ru
    · exact B.six_ONan
    · exact B.six_Co3
    · exact B.six_Co2
    · exact B.six_HN
    · exact B.six_Th
  seven_SL2 := rowSOf431_seven_SL2
  seven_SL3 := C.seven_SL3
  seven_SU3 := C.seven_SU3
  seven_Sp4 n hn := by
    by_cases h3 : n = 3
    · subst h3
      exact rowSOf431_sp4_eight
    · exact C.seven_Sp4_ne_three n hn h3
  seven_SU4 := C.seven_SU4
  seven_G2 := C.seven_G2
  seven_D4 := C.seven_D4
  seven_Sz := rowSOf431_seven_Sz
  seven_F4 := C.seven_F4
  seven_Tits := rowSOf431_seven_Tits
  eight_SL5 := rowSOf431_eight_SL5
  eight_SU5 := B.eight_SU5
  eight_SL6 := C.eight_SL6
  eight_SU6 := B.eight_SU6
  eight_SL7 := C.eight_SL7
  eight_Sp6 := rowSOf431_sp6_two
  eight_Sp8 := B.eight_Sp8
  eight_OmegaPlus := B.eight_OmegaPlus
  eight_OmegaMinus := C.eight_OmegaMinus
  eight_SL4 := C.eight_SL4
  eight_Sp6_4 := C.eight_Sp6_4
  eight_SU5_4 := rowSOf431_eight_SU5_4
  eight_SU5_8 := B.eight_SU5_8
  eight_F4 := C.eight_F4
  nine_SL3 e he he3 := by
    rcases (show e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl
    · exact rowSOf431_nine_SL3_odd 1 (Or.inl rfl)
    · exact B.nine_SL3_nine
    · exact rowSOf431_nine_SL3_odd 3 (Or.inr rfl)
  nine_SU3 e he he3 := by
    rcases (show e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl
    · exact rowSOf431_nine_SU3_odd 1 (Or.inl rfl)
    · exact B.nine_SU3_nine
    · exact rowSOf431_nine_SU3_odd 3 (Or.inr rfl)
  nine_G2 := rowSOf431_nine_G2
  nine_SL4 := B.nine_SL4
  nine_SU4 := W.nine_SU4

theorem item4_31List42_of_parts (B : K431OpenB) (C : K431OpenC) (D : K431OpenD) :
    Item4_31List42 :=
  item4_31List42_of_rowsS (k431RowsS_of_parts B C D k431OpenW)

theorem item4_31List42_of_inn (hI : CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed.I1430LieTwoInn)
    (hC : CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed.I1430LieTwoInn → K431OpenC)
    (B : K431OpenB) (D : K431OpenD) : Item4_31List42 :=
  item4_31List42_of_parts B (hC hI) D

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan431
