module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.A6
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataA6.A6b0c1w12
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataA6.A6b0c1w21
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataA6.A6b0c2
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataA6.A6b0c3
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataA6.A6b0c4
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataA6.A6b0c5
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataA6.A6b0c5w12
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellDataA6.A6b0c5w21

public section

namespace CFSG.StandardType.GGResQTwoCellDataA6

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def wits_A6_b0 (s : Fin 6 × ℤ × ℤ) : List (ℕ × ℕ × GGResQTwoCell 6) :=
  if s = (1, -1, -2) then wits_A6b0c1w12
  else if s = (1, -2, -1) then wits_A6b0c1w21
  else if s = (2, -1, -1) then wits_A6b0c2
  else if s = (3, -1, -1) then wits_A6b0c3
  else if s = (4, -1, -1) then wits_A6b0c4
  else if s = (5, -1, -1) then wits_A6b0c5
  else if s = (5, -1, -2) then wits_A6b0c5w12
  else if s = (5, -2, -1) then wits_A6b0c5w21
  else []

theorem cell_A6_b0 :
    GGResQTwoShapeCoverage (CartanMatrix.A 6) 0 (GGResIDisp.A6.shapes_A6_b0) (wits_A6_b0) := by
  intro s hs
  simp only [GGResIDisp.A6.shapes_A6_b0, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [wits_A6_b0, if_pos rfl]
    exact hwits_A6b0c1w12
  · simp only [wits_A6_b0, if_neg (by decide : ¬ (((1, -2, -1)) = ((1, -1, -2)))), if_pos rfl]
    exact hwits_A6b0c1w21
  · simp only [wits_A6_b0, if_neg (by decide : ¬ (((2, -1, -1)) = ((1, -1, -2)))), if_neg (by decide : ¬ (((2, -1, -1)) = ((1, -2, -1)))), if_pos rfl]
    exact hwits_A6b0c2
  · simp only [wits_A6_b0, if_neg (by decide : ¬ (((3, -1, -1)) = ((1, -1, -2)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((1, -2, -1)))), if_neg (by decide : ¬ (((3, -1, -1)) = ((2, -1, -1)))), if_pos rfl]
    exact hwits_A6b0c3
  · simp only [wits_A6_b0, if_neg (by decide : ¬ (((4, -1, -1)) = ((1, -1, -2)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((1, -2, -1)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((4, -1, -1)) = ((3, -1, -1)))), if_pos rfl]
    exact hwits_A6b0c4
  · simp only [wits_A6_b0, if_neg (by decide : ¬ (((5, -1, -1)) = ((1, -1, -2)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((1, -2, -1)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((3, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -1)) = ((4, -1, -1)))), if_pos rfl]
    exact hwits_A6b0c5
  · simp only [wits_A6_b0, if_neg (by decide : ¬ (((5, -1, -2)) = ((1, -1, -2)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((1, -2, -1)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((3, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((4, -1, -1)))), if_neg (by decide : ¬ (((5, -1, -2)) = ((5, -1, -1)))), if_pos rfl]
    exact hwits_A6b0c5w12
  · simp only [wits_A6_b0, if_neg (by decide : ¬ (((5, -2, -1)) = ((1, -1, -2)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((1, -2, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((2, -1, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((3, -1, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((4, -1, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((5, -1, -1)))), if_neg (by decide : ¬ (((5, -2, -1)) = ((5, -1, -2)))), if_pos rfl]
    exact hwits_A6b0c5w21
theorem hsideOK_A6_b0 :
    ∀ s ∈ GGResIDisp.A6.shapes_A6_b0, ∀ w ∈ wits_A6_b0 s,
      ggResQTwoCellSideOK (0 : Fin 6) w.2.2 := by
  have hall : (GGResIDisp.A6.shapes_A6_b0.all fun s => (wits_A6_b0 s).all fun w =>
      ggResQTwoCellSideOKB (0 : Fin 6) w.2.2) = true := by
    decide +kernel
  intro s hs w hw
  exact (ggResQTwoCellSideOKB_iff _ _).mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall s hs) w hw)

theorem hshapeNZ_A6_b0 :
    ∀ s ∈ GGResIDisp.A6.shapes_A6_b0, ((s.2.1 : ℤ) : ZMod 3) ≠ 0 := by
  have hall : (GGResIDisp.A6.shapes_A6_b0.all fun s => decide (((s.2.1 : ℤ) : ZMod 3) ≠ 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

end CFSG.StandardType.GGResQTwoCellDataA6
