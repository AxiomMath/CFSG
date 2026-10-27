module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Floor

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open Equiv Equiv.Perm

def e34x0 : alternatingGroup (Fin 5) := ⟨swap 0 1 * swap 1 2, by rw [mem_alternatingGroup]; decide⟩

def e34v1 : alternatingGroup (Fin 5) := ⟨swap 0 1 * swap 2 3, by rw [mem_alternatingGroup]; decide⟩
def e34v2 : alternatingGroup (Fin 5) := ⟨swap 0 2 * swap 1 3, by rw [mem_alternatingGroup]; decide⟩
def e34v3 : alternatingGroup (Fin 5) := ⟨swap 0 3 * swap 1 2, by rw [mem_alternatingGroup]; decide⟩

def e34V0 : Subgroup (alternatingGroup (Fin 5)) where
  carrier := {1, e34v1, e34v2, e34v3}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;> decide
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> decide

theorem e34V0_sq (g : alternatingGroup (Fin 5)) (hg : g ∈ e34V0) : g ^ 2 = 1 := by
  have hg' : g = 1 ∨ g = e34v1 ∨ g = e34v2 ∨ g = e34v3 := hg
  rcases hg' with rfl | rfl | rfl | rfl <;> decide

theorem e34x0_conj (g : alternatingGroup (Fin 5)) (hg : g ∈ e34V0) :
    e34x0 * g * e34x0⁻¹ ∈ e34V0 := by
  have hg' : g = 1 ∨ g = e34v1 ∨ g = e34v2 ∨ g = e34v3 := hg
  show _ ∈ ({1, e34v1, e34v2, e34v3} : Set _)
  rcases hg' with rfl | rfl | rfl | rfl <;> decide


theorem e34_a5_data {H : Type} [Group H] {K : Subgroup H}
    (e : K ≃* alternatingGroup (Fin 5)) :
    ∃ x ∈ K, orderOf x = 3 ∧ ∃ V : Subgroup H, V ≤ K ∧ IsPGroup 2 V ∧ V ≠ ⊥ ∧
      ∀ v ∈ V, x * v * x⁻¹ ∈ V := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨((e.symm e34x0 : K) : H), (e.symm e34x0).2, ?_,
    (e34V0.map e.symm.toMonoidHom).map K.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by decide) (by decide)
  · rw [isPGroup_iff_orderOf_dvd_pow]
    rintro ⟨g, hg⟩
    obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hg
    refine ⟨1, ?_⟩
    have h2 : (e.symm w) ^ 2 = 1 := by rw [← map_pow, e34V0_sq w hw, map_one]
    rw [← Subgroup.orderOf_coe]
    simp only [pow_one]
    exact orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val h2)
  · intro h
    have hmem : ((e.symm e34v1 : K) : H) ∈ (e34V0.map e.symm.toMonoidHom).map K.subtype :=
      ⟨_, ⟨e34v1, by show _ ∈ ({1, e34v1, e34v2, e34v3} : Set _); simp, rfl⟩, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    have : e.symm e34v1 = 1 := Subtype.ext hmem
    have := e.symm.injective (this.trans (map_one e.symm).symm)
    revert this
    decide
  · rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨_, ⟨e34x0 * w * e34x0⁻¹, e34x0_conj w hw, rfl⟩, ?_⟩
    simp

end CFSG.RankThree.PartTwo.Sec21.FF79
