module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuWord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

open Matrix

@[expose] def vecOf (v : ℕ) : Fin 6 → ZMod 2 := fun i => if v.testBit i then 1 else 0

@[expose] def trWord : Fin 64 → List (Bool × Fin 3) :=
  ![[], [(false, 0), (false, 1), (true, 0), (true, 1)], [(false, 1), (true, 1)],
    [(false, 1), (true, 0), (true, 1)], [], [(true, 1), (true, 0), (true, 1)], [(true, 1)],
    [(true, 0), (true, 1)], [(true, 2), (false, 2)],
    [(true, 2), (false, 2), (true, 1), (true, 0), (true, 1)], [(true, 2), (false, 2), (true, 1)],
    [(true, 2), (false, 2), (true, 0), (true, 1)], [(false, 2)],
    [(false, 2), (true, 1), (true, 0), (true, 1)], [(false, 2), (true, 1)],
    [(false, 2), (true, 0), (true, 1)], [(true, 1), (false, 1), (true, 2), (false, 2)],
    [(true, 1), (false, 1), (true, 2), (false, 2), (true, 1), (true, 0), (true, 1)],
    [(true, 1), (false, 1), (false, 2), (true, 1)],
    [(true, 1), (false, 1), (false, 2), (true, 0), (true, 1)], [(false, 2), (false, 1), (false, 2)],
    [(false, 2), (false, 1), (false, 2), (true, 1), (true, 0), (true, 1)],
    [(true, 1), (false, 1), (false, 2)], [(true, 0), (true, 1), (false, 1), (false, 2)],
    [(false, 1), (true, 2), (false, 2)],
    [(false, 1), (true, 2), (false, 2), (true, 1), (true, 0), (true, 1)],
    [(false, 1), (false, 2), (true, 1)], [(false, 1), (false, 2), (true, 0), (true, 1)],
    [(false, 1), (false, 2)], [(false, 1), (false, 2), (true, 1), (true, 0), (true, 1)],
    [(false, 1), (true, 2), (false, 2), (true, 1)],
    [(false, 1), (true, 2), (false, 2), (true, 0), (true, 1)],
    [(true, 0), (false, 0), (true, 1), (false, 1), (true, 2), (false, 2)],
    [(true, 0), (false, 0), (true, 1), (false, 1), (false, 2), (true, 0), (true, 1)],
    [(false, 1), (false, 2), (false, 1), (false, 0), (false, 1), (false, 2), (true, 1)],
    [(true, 0), (false, 0), (true, 1), (false, 1), (false, 2), (true, 1)],
    [(false, 2), (true, 0), (false, 0), (false, 1), (false, 2)],
    [(true, 0), (false, 0), (true, 0), (true, 1), (false, 1), (false, 2)],
    [(false, 2), (false, 1), (false, 0), (false, 1), (false, 2), (true, 1)],
    [(true, 0), (false, 0), (true, 1), (false, 1), (false, 2)],
    [(true, 0), (false, 0), (false, 1), (true, 2), (false, 2)],
    [(true, 0), (false, 0), (false, 1), (false, 2), (true, 0), (true, 1)],
    [(false, 1), (false, 0), (false, 1), (true, 2), (false, 2), (true, 1)],
    [(true, 0), (false, 0), (false, 1), (false, 2), (true, 1)],
    [(true, 0), (false, 0), (false, 1), (false, 2)],
    [(true, 0), (false, 0), (false, 1), (true, 2), (false, 2), (true, 0), (true, 1)],
    [(false, 1), (false, 0), (false, 1), (false, 2), (true, 1)],
    [(true, 0), (false, 0), (false, 1), (true, 2), (false, 2), (true, 1)],
    [(false, 0), (true, 1), (false, 1), (true, 2), (false, 2)],
    [(false, 0), (true, 1), (false, 1), (false, 2), (true, 0), (true, 1)],
    [(false, 0), (true, 1), (false, 1), (false, 2), (true, 1)],
    [(false, 0), (true, 1), (false, 1), (true, 2), (false, 2), (true, 1), (true, 0), (true, 1)],
    [(false, 2), (false, 0), (false, 1), (false, 2)],
    [(false, 0), (true, 0), (true, 1), (false, 1), (false, 2)],
    [(false, 0), (true, 1), (false, 1), (false, 2)],
    [(false, 2), (false, 0), (false, 1), (false, 2), (true, 1), (true, 0), (true, 1)],
    [(false, 0), (false, 1), (true, 2), (false, 2)],
    [(false, 0), (false, 1), (false, 2), (true, 0), (true, 1)],
    [(false, 0), (false, 1), (false, 2), (true, 1)],
    [(false, 0), (false, 1), (true, 2), (false, 2), (true, 1), (true, 0), (true, 1)],
    [(false, 0), (false, 1), (false, 2)],
    [(false, 0), (false, 1), (true, 2), (false, 2), (true, 0), (true, 1)],
    [(false, 0), (false, 1), (true, 2), (false, 2), (true, 1)],
    [(false, 0), (false, 1), (false, 2), (true, 1), (true, 0), (true, 1)]]

theorem trWord_spec : ∀ v : Fin 64, v ≠ 0 →
    toMat (rootBM (trWord v)) *ᵥ vecOf 4 = vecOf v := by
  decide +kernel

theorem rootProd_mem_closure (l : List (Bool × Fin 3)) :
    rootProd l ∈ Subgroup.closure ((Lgrp : Set G6) ∪ Set.range xE) := by
  induction l with
  | nil => exact Subgroup.one_mem _
  | cons a l ih =>
    rw [rootProd_cons]
    refine Subgroup.mul_mem _ ?_ ih
    obtain ⟨b, s⟩ := a
    cases b
    · exact Subgroup.subset_closure (Or.inl (yE_mem s))
    · exact Subgroup.subset_closure (Or.inr ⟨s, rfl⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis
