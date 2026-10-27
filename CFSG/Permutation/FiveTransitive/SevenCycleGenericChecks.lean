module

public import CFSG.Permutation.FiveTransitive.SmallSupportSeven

public section

namespace CFSG

namespace FiveTransitive.SevenCycleGeneric

open FiveTransitive.SmallSupportSeven

private def candidateWords10 (x y z : Fin 10) :
    List (Equiv.Perm (Fin 10)) :=
  let g := sevenCycle10
  let h := comparisonCycle10 x y z
  [g * h⁻¹, g ^ 2 * h⁻¹ ^ 2,
    g * h * g⁻¹ * h⁻¹, (g * h⁻¹) ^ 2]

private theorem exists_small_candidate10 :
    ∀ x y z : Fin 10,
      5 ≤ x.val → 5 ≤ y.val → 5 ≤ z.val →
      x ≠ y → x ≠ z → y ≠ z →
      ∃ w ∈ candidateWords10 x y z,
        w ≠ 1 ∧ w.support.card ≤ 5 := by
  decide +kernel

private theorem candidates10_mem_closure (x y z : Fin 10) :
    ∀ w ∈ candidateWords10 x y z,
      w ∈ Subgroup.closure
        ({sevenCycle10, comparisonCycle10 x y z} :
          Set (Equiv.Perm (Fin 10))) := by
  let K :=
    Subgroup.closure
      ({sevenCycle10, comparisonCycle10 x y z} :
        Set (Equiv.Perm (Fin 10)))
  have hg : sevenCycle10 ∈ K :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hh : comparisonCycle10 x y z ∈ K :=
    Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  intro w hw
  simp only [candidateWords10, List.mem_cons,
    List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact K.mul_mem hg (K.inv_mem hh)
  · exact
      K.mul_mem (K.pow_mem hg 2)
        (K.pow_mem (K.inv_mem hh) 2)
  · exact
      K.mul_mem
        (K.mul_mem (K.mul_mem hg hh) (K.inv_mem hg))
        (K.inv_mem hh)
  · exact
      K.pow_mem (K.mul_mem hg (K.inv_mem hh)) 2

theorem exists_small_mem_closure10
    (x y z : Fin 10)
    (hx : 5 ≤ x.val) (hy : 5 ≤ y.val) (hz : 5 ≤ z.val)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ w ∈ Subgroup.closure
        ({sevenCycle10, comparisonCycle10 x y z} :
          Set (Equiv.Perm (Fin 10))),
      w ≠ 1 ∧ w.support.card ≤ 5 := by
  obtain ⟨w, hw, hsmall⟩ :=
    exists_small_candidate10 x y z hx hy hz hxy hxz hyz
  exact
    ⟨w, candidates10_mem_closure x y z w hw, hsmall⟩

end FiveTransitive.SevenCycleGeneric

end CFSG
