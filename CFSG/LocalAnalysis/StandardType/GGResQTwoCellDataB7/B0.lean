module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.B7
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData

public section

namespace CFSG.StandardType.GGResQTwoCellDataB7

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def wits_B7_b0 (s : Fin 7 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 7) :=
  []

theorem cell_B7_b0 :
    GGResQTwoShapeCoverage (CartanMatrix.B 7) 0 (GGResIDisp.B7.shapes_B7_b0) (wits_B7_b0) := by
  intro s hs
  simp [GGResIDisp.B7.shapes_B7_b0] at hs
theorem hsideOK_B7_b0 :
    ∀ s ∈ GGResIDisp.B7.shapes_B7_b0, ∀ w ∈ wits_B7_b0 s,
      ggResQTwoCellSideOK (0 : Fin 7) w.2.2 := by
  have hall : (GGResIDisp.B7.shapes_B7_b0.all fun s => (wits_B7_b0 s).all fun w =>
      ggResQTwoCellSideOKB (0 : Fin 7) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_B7_b0 :
    ∀ s ∈ GGResIDisp.B7.shapes_B7_b0, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.B7.shapes_B7_b0.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

end CFSG.StandardType.GGResQTwoCellDataB7
