module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.E6
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataE6.E6b5c0
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataE6.E6b5c1

public section

namespace CFSG.StandardType.GGResQTwoCellDataE6

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def wits_E6_b5 (s : Fin 6 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 6) :=
  if s = (0, -1, -1) then wits_E6b5c0
  else if s = (1, -1, -1) then wits_E6b5c1
  else []

theorem cell_E6_b5 :
    GGResQTwoShapeCoverage (CartanMatrix.E 6) 5 (GGResIDisp.E6.shapes_E6_b5) (wits_E6_b5) := by
  intro s hs
  simp only [GGResIDisp.E6.shapes_E6_b5, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · simp only [wits_E6_b5, if_pos rfl]
    exact hwits_E6b5c0
  · simp only [wits_E6_b5, if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -1, -1)))), if_pos rfl]
    exact hwits_E6b5c1
theorem hsideOK_E6_b5 :
    ∀ s ∈ GGResIDisp.E6.shapes_E6_b5, ∀ w ∈ wits_E6_b5 s,
      ggResQTwoCellSideOK (5 : Fin 6) w.2.2 := by
  have hall : (GGResIDisp.E6.shapes_E6_b5.all fun s => (wits_E6_b5 s).all fun w =>
      ggResQTwoCellSideOKB (5 : Fin 6) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_E6_b5 :
    ∀ s ∈ GGResIDisp.E6.shapes_E6_b5, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.E6.shapes_E6_b5.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

end CFSG.StandardType.GGResQTwoCellDataE6
