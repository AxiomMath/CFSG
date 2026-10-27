module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.D7
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD7.D7b0c5
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD7.D7b0c6

public section

namespace CFSG.StandardType.GGResQTwoCellDataD7

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def wits_D7_b0 (s : Fin 7 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 7) :=
  if s = (5, -1, -1) then wits_D7b0c5
  else if s = (6, -1, -1) then wits_D7b0c6
  else []

theorem cell_D7_b0 :
    GGResQTwoShapeCoverage (CartanMatrix.D 7) 0 (GGResIDisp.D7.shapes_D7_b0) (wits_D7_b0) := by
  intro s hs
  simp only [GGResIDisp.D7.shapes_D7_b0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · simp only [wits_D7_b0, if_pos rfl]
    exact hwits_D7b0c5
  · simp only [wits_D7_b0, if_neg (by decide : ¬ (((6, -1, -1)) = ((5, -1, -1)))), if_pos rfl]
    exact hwits_D7b0c6
theorem hsideOK_D7_b0 :
    ∀ s ∈ GGResIDisp.D7.shapes_D7_b0, ∀ w ∈ wits_D7_b0 s,
      ggResQTwoCellSideOK (0 : Fin 7) w.2.2 := by
  have hall : (GGResIDisp.D7.shapes_D7_b0.all fun s => (wits_D7_b0 s).all fun w =>
      ggResQTwoCellSideOKB (0 : Fin 7) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_D7_b0 :
    ∀ s ∈ GGResIDisp.D7.shapes_D7_b0, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.D7.shapes_D7_b0.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

end CFSG.StandardType.GGResQTwoCellDataD7
