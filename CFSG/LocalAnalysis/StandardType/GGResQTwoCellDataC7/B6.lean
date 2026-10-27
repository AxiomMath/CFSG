module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.C7
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataC7.C7b6c0
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataC7.C7b6c0w12
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataC7.C7b6c0w21
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataC7.C7b6c1
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataC7.C7b6c2
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataC7.C7b6c3
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataC7.C7b6c4
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataC7.C7b6c5
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataC7.C7b6c5w12
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataC7.C7b6c5w21

public section

namespace CFSG.StandardType.GGResQTwoCellDataC7

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def wits_C7_b6 (s : Fin 7 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 7) :=
  if s = (0, -1, -1) then wits_C7b6c0
  else if s = (0, -1, -2) then wits_C7b6c0w12
  else if s = (0, -2, -1) then wits_C7b6c0w21
  else if s = (1, -1, -1) then wits_C7b6c1
  else if s = (2, -1, -1) then wits_C7b6c2
  else if s = (3, -1, -1) then wits_C7b6c3
  else if s = (4, -1, -1) then wits_C7b6c4
  else if s = (5, -1, -1) then wits_C7b6c5
  else if s = (5, -1, -2) then wits_C7b6c5w12
  else if s = (5, -2, -1) then wits_C7b6c5w21
  else []

theorem cell_C7_b6 :
    GGResQTwoShapeCoverage (CartanMatrix.C 7) 6 (GGResIDisp.C7.shapes_C7_b6) (wits_C7_b6) := by
  intro s hs
  simp only [GGResIDisp.C7.shapes_C7_b6, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [wits_C7_b6, if_pos rfl]
    exact hwits_C7b6c0
  · simp only [wits_C7_b6, if_neg (by decide : ¬ (((0, -1, -2)) = ((0, -1, -1)))), if_pos rfl]
    exact hwits_C7b6c0w12
  · simp only [wits_C7_b6, if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -2)))), if_pos rfl]
    exact hwits_C7b6c0w21
  · simp only [wits_C7_b6, if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -2, -1)))), if_pos rfl]
    exact hwits_C7b6c1
  · simp only [wits_C7_b6, if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((1, -1, -1)))), if_pos rfl]
    exact hwits_C7b6c2
  · simp only [wits_C7_b6, if_neg (by decide : ¬ (((3, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((2, -1, -1)))), if_pos rfl]
    exact hwits_C7b6c3
  · simp only [wits_C7_b6, if_neg (by decide : ¬ (((4, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((3, -1, -1)))), if_pos rfl]
    exact hwits_C7b6c4
  · simp only [wits_C7_b6, if_neg (by decide : ¬ (((5, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((3, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((4, -1, -1)))), if_pos rfl]
    exact hwits_C7b6c5
  · simp only [wits_C7_b6, if_neg (by decide : ¬ (((5, -1, -2)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((3, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((4, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((5, -1, -1)))), if_pos rfl]
    exact hwits_C7b6c5w12
  · simp only [wits_C7_b6, if_neg (by decide : ¬ (((5, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((3, -1, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((4, -1, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((5, -1, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((5, -1, -2)))), if_pos rfl]
    exact hwits_C7b6c5w21
theorem hsideOK_C7_b6 :
    ∀ s ∈ GGResIDisp.C7.shapes_C7_b6, ∀ w ∈ wits_C7_b6 s,
      ggResQTwoCellSideOK (6 : Fin 7) w.2.2 := by
  have hall : (GGResIDisp.C7.shapes_C7_b6.all fun s => (wits_C7_b6 s).all fun w =>
      ggResQTwoCellSideOKB (6 : Fin 7) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_C7_b6 :
    ∀ s ∈ GGResIDisp.C7.shapes_C7_b6, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.C7.shapes_C7_b6.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

end CFSG.StandardType.GGResQTwoCellDataC7
