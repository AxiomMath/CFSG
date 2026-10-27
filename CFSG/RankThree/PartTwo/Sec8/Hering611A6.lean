module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open Equiv

theorem exists_even_involution_of_order_three : ∀ x : Perm (Fin 6), x ^ 3 = 1 → x ≠ 1 →
    ∃ p : Perm (Fin 6), Perm.sign p = 1 ∧ p ^ 2 = 1 ∧ p ≠ 1 ∧
      p * (x * p * x⁻¹) = (x * p * x⁻¹) * p ∧ x * p * x⁻¹ ≠ p ∧
      x * (x * p * x⁻¹) * x⁻¹ = p * (x * p * x⁻¹) := by
  decide +kernel

theorem exists_involution_of_order_three {C : Type*} [Group C]
    (e : C ≃* alternatingGroup (Fin 6)) {x : C} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ p : C, p ^ 2 = 1 ∧ p ≠ 1 ∧ p * (x * p * x⁻¹) = (x * p * x⁻¹) * p ∧ x * p * x⁻¹ ≠ p ∧
      x * (x * p * x⁻¹) * x⁻¹ = p * (x * p * x⁻¹) := by
  have h3 : ((e x : alternatingGroup (Fin 6)) : Perm (Fin 6)) ^ 3 = 1 := by
    have := congrArg (fun y : alternatingGroup (Fin 6) => (y : Perm (Fin 6)))
      (show e x ^ 3 = 1 by rw [← map_pow, hx3, map_one])
    simpa using this
  have h1 : ((e x : alternatingGroup (Fin 6)) : Perm (Fin 6)) ≠ 1 := by
    intro h
    apply hx1
    apply e.injective
    apply Subtype.ext
    simpa using h
  obtain ⟨p, hsign, hp2, hp1, hcomm, hne, hrel⟩ := exists_even_involution_of_order_three _ h3 h1
  have hpmem : p ∈ alternatingGroup (Fin 6) := Perm.mem_alternatingGroup.mpr hsign
  refine ⟨e.symm ⟨p, hpmem⟩, ?_, ?_, ?_, ?_, ?_⟩
  · apply e.injective
    apply Subtype.ext
    simpa using hp2
  · intro h
    apply hp1
    have := congrArg (fun y => (e y : Perm (Fin 6))) h
    simpa using this
  · apply e.injective
    apply Subtype.ext
    simpa using hcomm
  · intro h
    apply hne
    have := congrArg (fun y => (e y : Perm (Fin 6))) h
    simpa using this
  · apply e.injective
    apply Subtype.ext
    simpa using hrel

end CFSG.RankThree.PartTwo.Sec8.Hering611
