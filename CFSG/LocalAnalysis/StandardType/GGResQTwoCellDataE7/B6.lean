module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.E7
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataE7.E7b6c0

public section

namespace CFSG.StandardType.GGResQTwoCellDataE7

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def wits_E7_b6 (s : Fin 7 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 7) :=
  if s = (0, -1, -1) then wits_E7b6c0
  else []

theorem cell_E7_b6 :
    GGResQTwoShapeCoverage (CartanMatrix.E 7) 6 (GGResIDisp.E7.shapes_E7_b6) (wits_E7_b6) := by
  intro s hs
  simp only [GGResIDisp.E7.shapes_E7_b6, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl
  · simp only [wits_E7_b6, if_pos rfl]
    exact hwits_E7b6c0
theorem hsideOK_E7_b6 :
    ∀ s ∈ GGResIDisp.E7.shapes_E7_b6, ∀ w ∈ wits_E7_b6 s,
      ggResQTwoCellSideOK (6 : Fin 7) w.2.2 := by
  have hall : (GGResIDisp.E7.shapes_E7_b6.all fun s => (wits_E7_b6 s).all fun w =>
      ggResQTwoCellSideOKB (6 : Fin 7) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_E7_b6 :
    ∀ s ∈ GGResIDisp.E7.shapes_E7_b6, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.E7.shapes_E7_b6.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

end CFSG.StandardType.GGResQTwoCellDataE7
