module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.C7
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData

public section

namespace CFSG.StandardType.GGResQTwoCellDataC7

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def wits_C7_b0 (s : Fin 7 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 7) :=
  []

theorem cell_C7_b0 :
    GGResQTwoShapeCoverage (CartanMatrix.C 7) 0 (GGResIDisp.C7.shapes_C7_b0) (wits_C7_b0) := by
  intro s hs
  simp [GGResIDisp.C7.shapes_C7_b0] at hs
theorem hsideOK_C7_b0 :
    ∀ s ∈ GGResIDisp.C7.shapes_C7_b0, ∀ w ∈ wits_C7_b0 s,
      ggResQTwoCellSideOK (0 : Fin 7) w.2.2 := by
  have hall : (GGResIDisp.C7.shapes_C7_b0.all fun s => (wits_C7_b0 s).all fun w =>
      ggResQTwoCellSideOKB (0 : Fin 7) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_C7_b0 :
    ∀ s ∈ GGResIDisp.C7.shapes_C7_b0, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.C7.shapes_C7_b0.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

end CFSG.StandardType.GGResQTwoCellDataC7
