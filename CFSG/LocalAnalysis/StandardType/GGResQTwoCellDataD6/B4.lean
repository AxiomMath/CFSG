module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.D6
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD6.D6b4c0
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD6.D6b4c0w12
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD6.D6b4c0w21
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD6.D6b4c1
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD6.D6b4c2
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD6.D6b4c5
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD6.D6b4c5w12
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataD6.D6b4c5w21

public section

namespace CFSG.StandardType.GGResQTwoCellDataD6

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def wits_D6_b4 (s : Fin 6 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 6) :=
  if s = (0, -1, -1) then wits_D6b4c0
  else if s = (0, -1, -2) then wits_D6b4c0w12
  else if s = (0, -2, -1) then wits_D6b4c0w21
  else if s = (1, -1, -1) then wits_D6b4c1
  else if s = (2, -1, -1) then wits_D6b4c2
  else if s = (5, -1, -1) then wits_D6b4c5
  else if s = (5, -1, -2) then wits_D6b4c5w12
  else if s = (5, -2, -1) then wits_D6b4c5w21
  else []

theorem cell_D6_b4 :
    GGResQTwoShapeCoverage (CartanMatrix.D 6) 4 (GGResIDisp.D6.shapes_D6_b4) (wits_D6_b4) := by
  intro s hs
  simp only [GGResIDisp.D6.shapes_D6_b4, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [wits_D6_b4, if_pos rfl]
    exact hwits_D6b4c0
  · simp only [wits_D6_b4, if_neg (by decide : ¬ (((0, -1, -2)) = ((0, -1, -1)))), if_pos rfl]
    exact hwits_D6b4c0w12
  · simp only [wits_D6_b4, if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((0, -2, -1)) = ((0, -1, -2)))), if_pos rfl]
    exact hwits_D6b4c0w21
  · simp only [wits_D6_b4, if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((1, -1, -1)) = ((0, -2, -1)))), if_pos rfl]
    exact hwits_D6b4c1
  · simp only [wits_D6_b4, if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((1, -1, -1)))), if_pos rfl]
    exact hwits_D6b4c2
  · simp only [wits_D6_b4, if_neg (by decide : ¬ (((5, -1, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((2, -1, -1)))), if_pos rfl]
    exact hwits_D6b4c5
  · simp only [wits_D6_b4, if_neg (by decide : ¬ (((5, -1, -2)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((5, -1, -1)))), if_pos rfl]
    exact hwits_D6b4c5w12
  · simp only [wits_D6_b4, if_neg (by decide : ¬ (((5, -2, -1)) = ((0, -1, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((0, -1, -2)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((0, -2, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((1, -1, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((5, -1, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((5, -1, -2)))), if_pos rfl]
    exact hwits_D6b4c5w21
theorem hsideOK_D6_b4 :
    ∀ s ∈ GGResIDisp.D6.shapes_D6_b4, ∀ w ∈ wits_D6_b4 s,
      ggResQTwoCellSideOK (4 : Fin 6) w.2.2 := by
  have hall : (GGResIDisp.D6.shapes_D6_b4.all fun s => (wits_D6_b4 s).all fun w =>
      ggResQTwoCellSideOKB (4 : Fin 6) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_D6_b4 :
    ∀ s ∈ GGResIDisp.D6.shapes_D6_b4, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.D6.shapes_D6_b4.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

end CFSG.StandardType.GGResQTwoCellDataD6
