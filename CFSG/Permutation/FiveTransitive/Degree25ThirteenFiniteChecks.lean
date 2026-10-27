module

public import Mathlib.GroupTheory.Perm.Cycle.Concrete

public section

namespace CFSG

namespace FiveTransitive.Degree25ThirteenFiniteChecks

open Equiv

@[expose] def thirteenCycle : Perm (Fin 25) :=
  List.formPerm [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

theorem thirteenCycle_isCycle : thirteenCycle.IsCycle := by
  apply List.isCycle_formPerm
  · decide
  · norm_num

theorem thirteenCycle_card_support :
    thirteenCycle.support.card = 13 := by
  decide

@[expose] def sourceTuple : Fin 12 → Fin 25 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13]

@[expose] def targetTuple : Fin 12 → Fin 25 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

theorem sourceTuple_injective : Function.Injective sourceTuple := by
  decide

theorem targetTuple_injective : Function.Injective targetTuple := by
  decide

theorem sourceTuple_ne_eleven (i : Fin 12) :
    sourceTuple i ≠ 11 := by
  fin_cases i <;> decide

theorem sourceTuple_ne_twelve (i : Fin 12) :
    sourceTuple i ≠ 12 := by
  fin_cases i <;> decide

theorem mem_range_targetTuple_iff (z : Fin 25) :
    z ∈ Set.range targetTuple ↔ z.val < 12 := by
  have hval (i : Fin 12) : (targetTuple i).val = i.val := by
    fin_cases i <;> decide
  constructor
  · rintro ⟨i, rfl⟩
    rw [hval]
    exact i.isLt
  · intro hz
    refine ⟨⟨z.val, hz⟩, Fin.ext ?_⟩
    rw [hval]

@[expose] def comparisonCycle (x y : Fin 25) : Perm (Fin 25) :=
  List.formPerm [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, x, y]

@[expose] def smallWord (x y : Fin 25) : Perm (Fin 25) :=
  thirteenCycle * (comparisonCycle x y)⁻¹

@[expose] def SmallWordPredicate (x y : Fin 25) : Prop :=
  12 ≤ x.val → 12 ≤ y.val → x ≠ y →
    smallWord x y ≠ 1 ∧ (smallWord x y).support.card ≤ 5

theorem smallWord_all :
    ∀ x y : Fin 25, SmallWordPredicate x y := by
  unfold SmallWordPredicate
  decide +kernel

theorem smallWord_mem_closure (x y : Fin 25) :
    smallWord x y ∈ Subgroup.closure
      ({thirteenCycle, comparisonCycle x y} : Set (Perm (Fin 25))) := by
  apply Subgroup.mul_mem
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · apply Subgroup.inv_mem
    exact Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_singleton _))

end FiveTransitive.Degree25ThirteenFiniteChecks

end CFSG
