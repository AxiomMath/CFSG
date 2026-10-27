module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL3Char3List
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL3Char3Outer
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.Item49Small

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.Assembly.RankThreeEven (projSL)

theorem outerRow_projSL_three_gf_nine : OuterRow (projSL 3 (GaloisField 3 2)) :=
  outerRow_of_not_three_dvd_outer
    (CFSG.RankThree.PartTwo.Sec4.Item49Small.not_three_dvd_card_outer_projSL (n := 3) (e := 2)
      (by norm_num) (by norm_num) (by norm_num))

theorem nat_card_galoisField_three_two : Nat.card (GaloisField 3 2) = 9 :=
  (GaloisField.card 3 2 (by norm_num)).trans (by norm_num)

theorem goodRow_projSL_three_gf_nine : GoodRow (projSL 3 (GaloisField 3 2)) :=
  ⟨listRow_projSL_three_char_three (le_of_eq nat_card_galoisField_three_two.symm),
    outerRow_projSL_three_gf_nine⟩

theorem goodRow_projSL_three_gf_twentyseven : GoodRow (projSL 3 (GaloisField 3 3)) :=
  ⟨listRow_projSL_three_char_three (by rw [nat_card_galoisField_three_three]; norm_num),
    outerRow_projSL_three_gf_twentyseven⟩

theorem rowOf_projSL_three_gf_nine : RowOf (projSL 3 (GaloisField 3 2)) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv e.symm goodRow_projSL_three_gf_nine

theorem rowOf_projSL_three_gf_twentyseven : RowOf (projSL 3 (GaloisField 3 3)) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv e.symm goodRow_projSL_three_gf_twentyseven

theorem rowOf_nine_SL3_ge_two : ∀ e : ℕ, 2 ≤ e → e ≤ 3 → RowOf (projSL 3 (GaloisField 3 e)) := by
  intro e he2 he3
  interval_cases e
  · exact rowOf_projSL_three_gf_nine
  · exact rowOf_projSL_three_gf_twentyseven

end CFSG.RankThree.PartTwo.Sec4.RonanK432
