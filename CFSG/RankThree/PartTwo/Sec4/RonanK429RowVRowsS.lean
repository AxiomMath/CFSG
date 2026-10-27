module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowsS
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVG23
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVU43
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVL2
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVL39

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429V

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem one_three : ∀ e : ℕ, 3 ≤ e → RowSOf429 (projSL 2 (GaloisField 3 e)) :=
  fun _ _ => rowSOf429_of_noCfg fun _ _ _ hs hna ⟨φ⟩ => RowV.noCfgS429_projSL_two_three hs hna φ

theorem nine_SL3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowSOf429 (projSL 3 (GaloisField 3 e)) := by
  intro e he1 he3
  refine rowSOf429_of_noCfg fun _ _ _ hs hna ⟨φ⟩ => ?_
  obtain rfl | rfl | rfl : e = 1 ∨ e = 2 ∨ e = 3 := by omega
  · exact RowV.noCfgS429_projSL_three_char_three (Or.inl rfl) φ
  · exact RowV.noCfgS429_projSL_three_nine hs hna φ
  · exact RowV.noCfgS429_projSL_three_char_three (Or.inr rfl) φ

theorem nine_SU3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowSOf429 (projSU 3 3 e) :=
  fun _ he1 he3 => rowSOf429_of_noCfg fun _ _ _ _ _ ⟨φ⟩ =>
    RowV.noCfgS429_projSU_three_char_three he1 he3 φ

theorem nine_SL4 : RowSOf429 (projSL 4 (GaloisField 3 1)) :=
  rowSOf429_of_noCfg fun _ _ _ _ _ ⟨φ⟩ => RowV.noCfgS429_projSL_four_three φ

theorem nine_SU4 : RowSOf429 (projSU 4 3 1) :=
  rowSOf429_of_noCfg fun _ _ _ hs hna ⟨φ⟩ => RowV.noCfgS429_projSU_four_three hs hna φ

theorem eight_SU5_4 : RowSOf429 (projSU 5 2 2) :=
  rowSOf429_of_noCfg fun _ _ _ _ _ ⟨φ⟩ => RowV.noCfgS429_projSU_five_four φ

theorem nine_G2 :
    RowSOf429 (TauCeti.CFSGIndex.lie g2ThreeIndex).Group :=
  rowSOf429_of_noCfg fun _ _ _ _ _ ⟨φ⟩ => RowV.noCfgS429_g2_three φ

end CFSG.RankThree.PartTwo.Sec4.RonanK429V
