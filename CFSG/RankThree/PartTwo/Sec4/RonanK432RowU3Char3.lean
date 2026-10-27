module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU3Char3Outer
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU3Char3One
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.Assembly.RankThreeEven (projSU)
open U3Char3

theorem goodRow_projSU_three_one : GoodRow (projSU 3 3 1) :=
  ⟨listRow_projSU_three_one, outerRow_projSU_three_one⟩

theorem rowOf_nine_SU3_one : RowOf (projSU 3 3 1) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv e.symm goodRow_projSU_three_one

theorem outerRow_projSU_three_gf_nine : OuterRow (projSU 3 3 2) :=
  outerRow_of_not_three_dvd_outer
    (CFSG.RankThree.PartTwo.Sec4.Item49Small.not_three_dvd_card_outer_projSU (n := 3) (e := 2)
      (by norm_num) (by norm_num) (by norm_num))

theorem goodRow_projSU_three_gf_nine : GoodRow (projSU 3 3 2) :=
  ⟨listRow_projSU_three_char_three le_rfl, outerRow_projSU_three_gf_nine⟩

theorem rowOf_nine_SU3_two : RowOf (projSU 3 3 2) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv e.symm goodRow_projSU_three_gf_nine

theorem outerRow_projSU_three_gf_twentyseven : OuterRow (projSU 3 3 3) := by
  obtain ⟨φ⟩ := CFSG.RankThree.PartTwo.KFacts.nonempty_unitaryPSU_mulEquiv_projSU
    unitaryFieldData_three_three
  exact OuterRow.of_mulEquiv φ outerRow_unitaryPSU_gf_twentyseven

theorem goodRow_projSU_three_gf_twentyseven : GoodRow (projSU 3 3 3) :=
  ⟨listRow_projSU_three_char_three (by norm_num), outerRow_projSU_three_gf_twentyseven⟩

theorem rowOf_nine_SU3_three : RowOf (projSU 3 3 3) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv e.symm goodRow_projSU_three_gf_twentyseven

theorem rowOf_nine_SU3_ge_two : ∀ e : ℕ, 2 ≤ e → e ≤ 3 → RowOf (projSU 3 3 e) := by
  intro e he2 he3
  interval_cases e
  · exact rowOf_nine_SU3_two
  · exact rowOf_nine_SU3_three

theorem rowOf_nine_SU3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowOf (projSU 3 3 e) := by
  intro e he1 he3
  rcases Nat.lt_or_ge e 2 with h | h
  · obtain rfl : e = 1 := by omega
    exact rowOf_nine_SU3_one
  · exact rowOf_nine_SU3_ge_two e h he3

end CFSG.RankThree.PartTwo.Sec4.RonanK432
