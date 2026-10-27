module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.D7
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD7.D7b5c0
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD7.D7b5c0w12
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD7.D7b5c0w21
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD7.D7b5c1
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD7.D7b5c2
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD7.D7b5c3
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD7.D7b5c6
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD7.D7b5c6w12
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD7.D7b5c6w21

public section

namespace CFSG.StandardType.GGResQTwoCellDataD7

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def wits_D7_b5 (s : Fin 7 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 7) :=
  if s = (0, -1, -1) then wits_D7b5c0
  else if s = (0, -1, -2) then wits_D7b5c0w12
  else if s = (0, -2, -1) then wits_D7b5c0w21
  else if s = (1, -1, -1) then wits_D7b5c1
  else if s = (2, -1, -1) then wits_D7b5c2
  else if s = (3, -1, -1) then wits_D7b5c3
  else if s = (6, -1, -1) then wits_D7b5c6
  else if s = (6, -1, -2) then wits_D7b5c6w12
  else if s = (6, -2, -1) then wits_D7b5c6w21
  else []

theorem cell_D7_b5 :
    GGResQTwoShapeCoverage (CartanMatrix.D 7) 5 (GGResIDisp.D7.shapes_D7_b5) (wits_D7_b5) := by
  intro s hs
  simp only [GGResIDisp.D7.shapes_D7_b5, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [wits_D7_b5, if_pos rfl]
    exact hwits_D7b5c0
  · simp only [wits_D7_b5, if_neg (by decide : ¬ (((0, -1, -2)) = ((0, -1, -1)))), if_pos rfl]
    exact hwits_D7b5c0w12
  · simp only [wits_D7_b5, if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -2)))), if_pos rfl]
    exact hwits_D7b5c0w21
  · simp only [wits_D7_b5, if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -2, -1)))), if_pos rfl]
    exact hwits_D7b5c1
  · simp only [wits_D7_b5, if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((1, -1, -1)))), if_pos rfl]
    exact hwits_D7b5c2
  · simp only [wits_D7_b5, if_neg (by decide : ¬ (((3, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((2, -1, -1)))), if_pos rfl]
    exact hwits_D7b5c3
  · simp only [wits_D7_b5, if_neg (by decide : ¬ (((6, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((6, -1, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((6, -1, -1)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -1)) = ((3, -1, -1)))), if_pos rfl]
    exact hwits_D7b5c6
  · simp only [wits_D7_b5, if_neg (by decide : ¬ (((6, -1, -2)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -2)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((6, -1, -2)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((6, -1, -2)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -2)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -2)) = ((3, -1, -1)))), if_neg (by decide : ¬ (((6, -1, -2)) = ((6, -1, -1)))), if_pos rfl]
    exact hwits_D7b5c6w12
  · simp only [wits_D7_b5, if_neg (by decide : ¬ (((6, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((3, -1, -1)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((6, -1, -1)))), if_neg (by decide : ¬ (((6, -2, -1)) = ((6, -1, -2)))), if_pos rfl]
    exact hwits_D7b5c6w21
theorem hsideOK_D7_b5 :
    ∀ s ∈ GGResIDisp.D7.shapes_D7_b5, ∀ w ∈ wits_D7_b5 s,
      ggResQTwoCellSideOK (5 : Fin 7) w.2.2 := by
  have hall : (GGResIDisp.D7.shapes_D7_b5.all fun s => (wits_D7_b5 s).all fun w =>
      ggResQTwoCellSideOKB (5 : Fin 7) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_D7_b5 :
    ∀ s ∈ GGResIDisp.D7.shapes_D7_b5, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.D7.shapes_D7_b5.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

end CFSG.StandardType.GGResQTwoCellDataD7
