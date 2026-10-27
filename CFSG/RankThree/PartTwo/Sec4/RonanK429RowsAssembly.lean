module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429Cover
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowAlt
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowL2
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowA9
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieFinal
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVRowsS
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHJ3
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHMcL
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHON
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHHN
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHTh
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieF4
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieSzTits
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowL52
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowR27
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHCo3
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHCo2
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHSuz
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHLy
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowRankTwo
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVRowsS2
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowA1112
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieU4Odd
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowESU5
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHL4
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHU4
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVRowsS3
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFF4
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFL6
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFL7
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFOm8
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowEO8
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowEU6

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)

theorem mod_three_eq_one_or_two_of_prime {p : ℕ} [hp : Fact p.Prime] (h3 : 3 < p) :
    p % 3 = 1 ∨ p % 3 = 2 := by
  have h0 : p % 3 ≠ 0 := fun h => by
    have := hp.out.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h)
    omega
  omega

section Assembly

theorem six_holds : ∀ s ∈ sporadics42, RowSOf429 (Spor s) := by
  intro s hs
  simp only [sporadics42, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rowSOf429_m11
  · exact rowSOf429_m12
  · exact rowSOf429_m22
  · exact rowSOf429_m23
  · exact rowSOf429_m24
  · exact rowSOf429_j1
  · exact rowSOf429_j2
  · exact RonanK429H.rowSOf429_j3
  · exact rowSOf429_j4
  · exact RonanK429H.rowSOf429_mcl
  · exact RonanK429H.rowSOf429_ly
  · exact rowSOf429_hs
  · exact rowSOf429_he
  · exact RonanK429H.rowSOf429_suz
  · exact rowSOf429_ru
  · exact RonanK429H.rowSOf429_on
  · exact RonanK429H.rowSOf429_co3
  · exact RonanK429H.rowSOf429_co2
  · exact RonanK429H.rowSOf429_hn
  · exact RonanK429H.rowSOf429_th

theorem k429RowsS_holds : K429RowsS where
  one p e _ _ he := by
    by_cases h : p = 3 ∧ 3 ≤ e
    · obtain ⟨rfl, h3⟩ := h
      exact RonanK429V.one_three e h3
    · exact rowSOf429_one p e he (by omega)
  two_SL := rowSOf429_two_SL
  two_SU := rowSOf429_two_SU
  three := rowSOf429_three
  four_G2 := rowSOf429_four_G2
  four_Sp := rowSOf429_four_Sp
  four_SL p _ hp := by
    rcases mod_three_eq_one_or_two_of_prime (p := p) hp with h | h
    · exact RonanK429H.rowSOf429_four_SL_mod_one p hp h
    · exact rowSOf429_four_SL_of_mod_two p hp h
  four_SU p _ hp := by
    rcases mod_three_eq_one_or_two_of_prime (p := p) hp with h | h
    · exact rowSOf429_four_SU_of_mod_one p hp h
    · exact RonanK429H.rowSOf429_four_SU_mod_two p hp h
  five n hn5 hn12 := by
    by_cases h8 : n ≤ 8
    · exact rowSOf429_alternating_le_eight hn5 h8
    · rcases (show n = 9 ∨ n = 10 ∨ 11 ≤ n by omega) with rfl | rfl | h11
      · exact rowSOf429_alternatingGroup_nine
      · exact rowSOf429_alternatingGroup_ten
      · exact rowSOf429_five_eleven n h11 hn12
  six := six_holds
  seven_SL2 := rowSOf429_seven_SL2
  seven_SL3 := RonanK429Lie.seven_SL3
  seven_SU3 := RonanK429Lie.seven_SU3
  seven_Sp4 := RonanK429Lie.seven_Sp4
  seven_SU4 := RonanK429Lie.seven_SU4
  seven_G2 := RonanK429Lie.seven_G2
  seven_D4 := RonanK429Lie.seven_D4
  seven_Sz := RonanK429Lie.seven_Sz
  seven_F4 := RonanK429Lie.seven_F4
  seven_Tits := RonanK429Lie.seven_Tits
  eight_SL5 := rowSOf429_eight_SL5
  eight_SU5 := RonanK429E.eight_SU5
  eight_SL6 := RonanK429F.eight_SL6
  eight_SU6 := RonanK429E.eight_SU6
  eight_SL7 := RonanK429F.eight_SL7
  eight_Sp6 := RonanK429E.eight_Sp6
  eight_Sp8 := RonanK429F.eight_Sp8
  eight_OmegaPlus := RonanK429E.eight_OmegaPlus
  eight_OmegaMinus := RonanK429F.eight_OmegaMinus
  eight_SL4 := RonanK429V.eight_SL4
  eight_Sp6_4 := RonanK429V.eight_Sp6_4
  eight_SU5_4 := RonanK429V.eight_SU5_4
  eight_SU5_8 := RonanK429V.eight_SU5_8
  eight_F4 := RonanK429F.eight_F4
  nine_SL3 := RonanK429V.nine_SL3
  nine_SU3 := RonanK429V.nine_SU3
  nine_G2 := RonanK429V.nine_G2
  nine_SL4 := RonanK429V.nine_SL4
  nine_SU4 := RonanK429V.nine_SU4

end Assembly

section Census

theorem item4_29_holds
    : Item4_29 :=
  item4_29_of_rowsS k429RowsS_holds k429CoverL3

end Census

end CFSG.RankThree.PartTwo.Sec4.RonanK429
