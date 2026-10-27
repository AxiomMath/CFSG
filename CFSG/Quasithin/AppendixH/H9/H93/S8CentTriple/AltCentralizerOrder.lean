module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ASVolI.ChH

open Equiv

theorem nat_card_altInfCentralizer_triple {u : Perm (Fin 8)} (hu : u.cycleType = {2, 2, 2}) :
    Nat.card ↥(alternatingGroup (Fin 8) ⊓ Subgroup.centralizer ({u} : Set (Perm (Fin 8)))) =
      48 := by
  have hC : Nat.card ↥(Subgroup.centralizer ({u} : Set (Perm (Fin 8)))) = 96 := by
    rw [Perm.nat_card_centralizer, hu]
    decide
  have hsign : Perm.sign u = -1 := by
    rw [Perm.sign_of_cycleType, hu]
    decide
  have h2 : (alternatingGroup (Fin 8)).relIndex
      (Subgroup.centralizer ({u} : Set (Perm (Fin 8)))) = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨u, Subgroup.mem_centralizer_iff.mpr (by rintro h rfl; rfl), ?_, fun b _ => ?_⟩
    · rw [Perm.mem_alternatingGroup, hsign]
      decide
    · rcases Int.units_eq_one_or (Perm.sign b) with h | h
      · exact Or.inr (Perm.mem_alternatingGroup.mpr h)
      · refine Or.inl (Perm.mem_alternatingGroup.mpr ?_)
        rw [map_mul, h, hsign]
        decide
  have h := Subgroup.relIndex_mul_card (alternatingGroup (Fin 8))
    (Subgroup.centralizer ({u} : Set (Perm (Fin 8))))
  rw [h2, hC] at h
  omega

end CFSG.ASVolI.ChH
