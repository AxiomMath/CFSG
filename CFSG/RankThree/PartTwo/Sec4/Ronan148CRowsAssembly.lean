module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148CSeitzRest
public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRowAlt
public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRowVac
public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRowCo2
public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRowLy
public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRowL2Three

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)


structure K148OpenRows : Prop where
  three : ∀ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
    RowSOf148 (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group
  six_J3 : RowSOf148 (Spor .J3)
  six_McL : RowSOf148 (Spor .McL)
  six_Suz : RowSOf148 (Spor .Suz)
  six_ONan : RowSOf148 (Spor .ONan)
  six_Co3 : RowSOf148 (Spor .Co3)
  six_HN : RowSOf148 (Spor .HN)
  six_Th : RowSOf148 (Spor .Th)
  nine_SL3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowSOf148 (projSL 3 (GaloisField 3 e))
  nine_SU3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowSOf148 (projSU 3 3 e)
  nine_G2 : RowSOf148 (TauCeti.CFSGIndex.lie g2ThreeIndex).Group
  nine_SL4 : RowSOf148 (projSL 4 (GaloisField 3 1))
  nine_SU4 : RowSOf148 (projSU 4 3 1)

section Certs


theorem six_of_open
    (O : K148OpenRows) : ∀ s ∈ sporadics42, RowSOf148 (Spor s) := by
  intro s hs
  simp only [sporadics42, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rowSOf148_m11
  · exact rowSOf148_m12
  · exact rowSOf148_m22
  · exact rowSOf148_m23
  · exact rowSOf148_m24
  · exact rowSOf148_j1
  · exact rowSOf148_j2
  · exact O.six_J3
  · exact rowSOf148_j4
  · exact O.six_McL
  · exact rowSOf148_ly
  · exact rowSOf148_hs
  · exact rowSOf148_he
  · exact O.six_Suz
  · exact rowSOf148_ru
  · exact O.six_ONan
  · exact O.six_Co3
  · exact rowSOf148_co2
  · exact O.six_HN
  · exact O.six_Th

theorem k148RowsS_of_open
    (hS : Seitz82Rest) (O : K148OpenRows) : K148RowsS :=
  K148RowsS.ofSeitz (Seitz82Balance.ofRest hS) rowSOf148_one_three O.three
    (fun _ hn5 hn12 => rowSOf148_alternating hn5 hn12) (six_of_open O) O.nine_SL3 O.nine_SU3
    O.nine_G2 O.nine_SL4 O.nine_SU4

end Certs

end CFSG.RankThree.PartTwo.Sec4.Ronan148C
