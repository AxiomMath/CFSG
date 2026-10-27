module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.E7
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataE7.E7b1c0
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataE7.E7b1c0w12
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataE7.E7b1c0w21
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataE7.E7b1c2
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataE7.E7b1c4
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataE7.E7b1c5
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataE7.E7b1c6
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataE7.E7b1c6w12
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataE7.E7b1c6w21

public section

namespace CFSG.StandardType.GGResQTwoCellDataE7

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def wits_E7_b1 (s : Fin 7 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 7) :=
  if s = (0, -1, -1) then wits_E7b1c0
  else if s = (0, -1, -2) then wits_E7b1c0w12
  else if s = (0, -2, -1) then wits_E7b1c0w21
  else if s = (2, -1, -1) then wits_E7b1c2
  else if s = (4, -1, -1) then wits_E7b1c4
  else if s = (5, -1, -1) then wits_E7b1c5
  else if s = (6, -1, -1) then wits_E7b1c6
  else if s = (6, -1, -2) then wits_E7b1c6w12
  else if s = (6, -2, -1) then wits_E7b1c6w21
  else []

theorem cell_E7_b1 :
    GGResQTwoShapeCoverage (CartanMatrix.E 7) 1 (GGResIDisp.E7.shapes_E7_b1) (wits_E7_b1) := by
  intro s hs
  simp only [GGResIDisp.E7.shapes_E7_b1, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [wits_E7_b1, if_pos rfl]
    exact hwits_E7b1c0
  · simp only [wits_E7_b1, if_neg (by decide : ¬ (((0, -1, -2)) = ((0, -1, -1)))), if_pos rfl]
    exact hwits_E7b1c0w12
  · simp only [wits_E7_b1, if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -2)))), if_pos rfl]
    exact hwits_E7b1c0w21
  · simp only [wits_E7_b1, if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -2, -1)))), if_pos rfl]
    exact hwits_E7b1c2
  · simp only [wits_E7_b1, if_neg (by decide : ¬ (((4, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((2, -1, -1)))), if_pos rfl]
    exact hwits_E7b1c4
  · simp only [wits_E7_b1, if_neg (by decide : ¬ (((5, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((4, -1, -1)))), if_pos rfl]
    exact hwits_E7b1c5
  · simp only [wits_E7_b1, if_neg (by decide : ¬ (((6, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((6, -1, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((6, -1, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -1)) = ((4, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -1)) = ((5, -1, -1)))), if_pos rfl]
    exact hwits_E7b1c6
  · simp only [wits_E7_b1, if_neg (by decide : ¬ (((6, -1, -2)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -2)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((6, -1, -2)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((6, -1, -2)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -2)) = ((4, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -2)) = ((5, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -2)) = ((6, -1, -1)))), if_pos rfl]
    exact hwits_E7b1c6w12
  · simp only [wits_E7_b1, if_neg (by decide : ¬ (((6, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((4, -1, -1)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((5, -1, -1)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((6, -1, -1)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((6, -1, -2)))), if_pos rfl]
    exact hwits_E7b1c6w21
theorem hsideOK_E7_b1 :
    ∀ s ∈ GGResIDisp.E7.shapes_E7_b1, ∀ w ∈ wits_E7_b1 s,
      ggResQTwoCellSideOK (1 : Fin 7) w.2.2 := by
  have hall : (GGResIDisp.E7.shapes_E7_b1.all fun s => (wits_E7_b1 s).all fun w =>
      ggResQTwoCellSideOKB (1 : Fin 7) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_E7_b1 :
    ∀ s ∈ GGResIDisp.E7.shapes_E7_b1, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.E7.shapes_E7_b1.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

end CFSG.StandardType.GGResQTwoCellDataE7
