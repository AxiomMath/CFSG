module

public import Mathlib.GroupTheory.Perm.Cycle.Concrete

public section

namespace CFSG

namespace FiveTransitive.Degree24ElevenFiniteChecks

open Equiv

@[expose] def elevenCycle : Perm (Fin 24) :=
  List.formPerm [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

theorem elevenCycle_isCycle : elevenCycle.IsCycle := by
  apply List.isCycle_formPerm
  · decide
  · norm_num

theorem elevenCycle_card_support :
    elevenCycle.support.card = 11 := by
  decide

@[expose] def sourceTuple : Fin 10 → Fin 24 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 11]

@[expose] def targetTuple : Fin 10 → Fin 24 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

theorem sourceTuple_injective : Function.Injective sourceTuple := by
  decide

theorem targetTuple_injective : Function.Injective targetTuple := by
  decide

theorem sourceTuple_ne_nine (i : Fin 10) :
    sourceTuple i ≠ 9 := by
  fin_cases i <;> decide

theorem sourceTuple_ne_ten (i : Fin 10) :
    sourceTuple i ≠ 10 := by
  fin_cases i <;> decide

theorem mem_range_targetTuple_iff (z : Fin 24) :
    z ∈ Set.range targetTuple ↔ z.val < 10 := by
  fin_cases z <;> simp [targetTuple]

@[expose] def comparisonCycle (x y : Fin 24) : Perm (Fin 24) :=
  List.formPerm [0, 1, 2, 3, 4, 5, 6, 7, 8, x, y]

@[expose] def smallWord (x y : Fin 24) : Perm (Fin 24) :=
  elevenCycle * (comparisonCycle x y)⁻¹

@[expose] def SmallWordPredicate (x y : Fin 24) : Prop :=
  10 ≤ x.val → 10 ≤ y.val → x ≠ y →
    smallWord x y ≠ 1 ∧ (smallWord x y).support.card ≤ 5

theorem smallWord_all :
    ∀ x y : Fin 24, SmallWordPredicate x y := by
  unfold SmallWordPredicate
  decide +kernel

theorem smallWord_mem_closure (x y : Fin 24) :
    smallWord x y ∈ Subgroup.closure
      ({elevenCycle, comparisonCycle x y} : Set (Perm (Fin 24))) := by
  apply Subgroup.mul_mem
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · apply Subgroup.inv_mem
    exact Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_singleton _))

end FiveTransitive.Degree24ElevenFiniteChecks

end CFSG
