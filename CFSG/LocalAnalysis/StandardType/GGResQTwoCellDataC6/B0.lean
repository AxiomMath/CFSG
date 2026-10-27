module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.C6
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData

public section

namespace CFSG.StandardType.GGResQTwoCellDataC6

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def wits_C6_b0 (s : Fin 6 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 6) :=
  []

theorem cell_C6_b0 :
    GGResQTwoShapeCoverage (CartanMatrix.C 6) 0 (GGResIDisp.C6.shapes_C6_b0) (wits_C6_b0) := by
  intro s hs
  simp [GGResIDisp.C6.shapes_C6_b0] at hs
theorem hsideOK_C6_b0 :
    ∀ s ∈ GGResIDisp.C6.shapes_C6_b0, ∀ w ∈ wits_C6_b0 s,
      ggResQTwoCellSideOK (0 : Fin 6) w.2.2 := by
  have hall : (GGResIDisp.C6.shapes_C6_b0.all fun s => (wits_C6_b0 s).all fun w =>
      ggResQTwoCellSideOKB (0 : Fin 6) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_C6_b0 :
    ∀ s ∈ GGResIDisp.C6.shapes_C6_b0, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.C6.shapes_C6_b0.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

end CFSG.StandardType.GGResQTwoCellDataC6
