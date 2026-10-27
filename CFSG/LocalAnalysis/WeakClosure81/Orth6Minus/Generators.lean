module

import CFSG.ClassicalGroups.Orthogonal.SumSquaresSigns
public import CFSG.LocalAnalysis.WeakClosure81.Orth6Minus.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Orth6Minus

open CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

private lemma permA_eq_commutator :
    permA = ⁅Equiv.swap (coord 0) (coord 1),
      Equiv.swap (coord 0) (coord 2) * Equiv.swap (coord 1) (coord 3)⁆ := by
  decide

private lemma permC_eq_commutator :
    permC = ⁅Equiv.swap (coord 2) (coord 4),
      Equiv.swap (coord 2) (coord 3) * Equiv.swap (coord 4) (coord 5)⁆ := by
  decide

theorem closure_gens_le_commutator (K : Type*) [Field K] :
    Subgroup.closure (gens K) ≤ ⁅orthSix K, orthSix K⁆ := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [gens, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hg
  rcases hg with ⟨r, s, hrs, rfl⟩ | rfl | rfl
  · exact negCoordGL_pair_mem_commutator hrs
  · rw [permA_eq_commutator]
    exact permutationGL_commutatorElement_mem_commutator _ _
  · rw [permC_eq_commutator]
    exact permutationGL_commutatorElement_mem_commutator _ _

end CFSG.LocalAnalysis.WeakClosure81.Orth6Minus
