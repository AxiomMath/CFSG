module

public import Mathlib.Data.Fin.VecNotation
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly

theorem frameCartan_intCartan_E7 : GGIntCartan CoxeterMatrix.E₇ (CartanMatrix.E 7) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i <;> decide
  · fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

theorem frameCartan_intCartan_E8 : GGIntCartan CoxeterMatrix.E₈ (CartanMatrix.E 8) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i <;> decide
  · fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

theorem frameCartan_entries_E7 : ∀ i j : Fin 7, i ≠ j →
    CartanMatrix.E 7 i j = 0 ∨ CartanMatrix.E 7 i j = -1 ∨ CartanMatrix.E 7 i j = -2 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

theorem frameCartan_entries_E8 : ∀ i j : Fin 8, i ≠ j →
    CartanMatrix.E 8 i j = 0 ∨ CartanMatrix.E 8 i j = -1 ∨ CartanMatrix.E 8 i j = -2 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

theorem frameCartan_tree_E7 : SecFiveRootRefl.CartanTree (CartanMatrix.E 7) := by
  refine ⟨![0, 3, 0, 2, 3, 4, 5], 0, ![0, 3, 1, 2, 3, 4, 5], fun i j hij => ?_, fun i hi => ?_⟩
  · fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  · fin_cases i <;> first | exact absurd rfl hi | decide

theorem frameCartan_tree_E8 : SecFiveRootRefl.CartanTree (CartanMatrix.E 8) := by
  refine ⟨![0, 3, 0, 2, 3, 4, 5, 6], 0, ![0, 3, 1, 2, 3, 4, 5, 6], fun i j hij => ?_, fun i hi => ?_⟩
  · fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  · fin_cases i <;> first | exact absurd rfl hi | decide

end CFSG.StandardType.FrameRoute

end
