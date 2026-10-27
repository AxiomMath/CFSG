module

public import CFSG.Quasithin.AppendixH.H9.H93.S8Struct
import CFSG.Quasithin.AppendixH.H9.H93.S8Classes.ExplicitE16
import CFSG.Quasithin.AppendixH.H9.H93.S8Classes.OrbitConj
import CFSG.Quasithin.AppendixH.H9.H93.S8Classes.PartitionMatching
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ASVolI.ChH

open Equiv

theorem orbitSizesOf_map_conj (B : Subgroup (Perm (Fin 8))) (g : Perm (Fin 8)) :
    orbitSizesOf (B.map (MulAut.conj g).toMonoidHom) = orbitSizesOf B :=
  E16Orbits.orbitSizesOf_conj B g

theorem exists_e16_with_orbitSizes {s : Multiset ℕ}
    (hs : s = {4, 4} ∨ s = {4, 2, 2} ∨ s = {2, 2, 2, 2}) :
    ∃ E : Subgroup (Perm (Fin 8)), IsElemAb2 E ∧ Nat.card E = 16 ∧ orbitSizesOf E = s := by
  rcases hs with rfl | rfl | rfl
  · exact ⟨e16Orbits44, isElemAb2_e16Orbits44, card_e16Orbits44, orbitSizesOf_e16Orbits44⟩
  · exact ⟨e16Orbits422, isElemAb2_e16Orbits422, card_e16Orbits422, orbitSizesOf_e16Orbits422⟩
  · exact ⟨e16Orbits2222, isElemAb2_e16Orbits2222, card_e16Orbits2222,
      orbitSizesOf_e16Orbits2222⟩

theorem exists_conj_of_orbitSizes_eq {E E' : Subgroup (Perm (Fin 8))} (hE : IsElemAb2 E)
    (hc : Nat.card E = 16) (hE' : IsElemAb2 E') (hc' : Nat.card E' = 16)
    (h : orbitSizesOf E = orbitSizesOf E') :
    ∃ g : Perm (Fin 8), E.map (MulAut.conj g).toMonoidHom = E' := by
  classical
  have key : ∀ B : Subgroup (Perm (Fin 8)),
      (Finset.univ.image fun x : Fin 8 => (MulAction.orbit B x : Set (Fin 8))).val.map
        (fun c => (Finset.univ.filter fun x : Fin 8 =>
          (MulAction.orbit B x : Set (Fin 8)) = c).card) = orbitSizesOf B := by
    intro B
    unfold orbitSizesOf
    refine Multiset.map_congr rfl fun c hc => ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_def.mpr hc)
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [MulAction.orbit_eq_iff]
  obtain ⟨g, hg⟩ := exists_perm_matching_fibers
    (fun x : Fin 8 => (MulAction.orbit E x : Set (Fin 8)))
    (fun x : Fin 8 => (MulAction.orbit E' x : Set (Fin 8))) (by rw [key E, key E', h])
  refine ⟨g, E16Orbits.eq_of_orbit_eq (E16Orbits.isElemAb2_map_conj hE g)
    (by rw [E16Orbits.card_map_conj, hc]) hE' hc' fun x' => ?_⟩
  obtain ⟨x, rfl⟩ := g.surjective x'
  rw [E16Orbits.orbit_map_conj]
  ext y'
  obtain ⟨y, rfl⟩ := g.surjective y'
  have h1 : y ∈ MulAction.orbit E x ↔ g y ∈ MulAction.orbit E' (g x) := by
    rw [← MulAction.orbit_eq_iff, ← MulAction.orbit_eq_iff]
    exact hg y x
  simpa using h1

theorem e16_le_alternatingGroup_iff {E : Subgroup (Perm (Fin 8))} (hE : IsElemAb2 E)
    (hc : Nat.card E = 16) :
    E ≤ alternatingGroup (Fin 8) ↔ orbitSizesOf E = {4, 4} := by
  constructor
  · intro hA
    by_contra hne
    have key : ∀ E0 : Subgroup (Perm (Fin 8)), swap (4 : Fin 8) 5 ∈ E0 →
        (∃ g : Perm (Fin 8), E0.map (MulAut.conj g).toMonoidHom = E) → False := by
      rintro E0 hsw ⟨g, hg⟩
      have hmem : g * swap (4 : Fin 8) 5 * g⁻¹ ∈ E := hg ▸ Subgroup.mem_map_of_mem _ hsw
      have := Perm.mem_alternatingGroup.mp (hA hmem)
      rw [E16Orbits.sign_conj_eq, Perm.sign_swap (by decide)] at this
      exact absurd this (by decide)
    rcases orbitSizes_of_e16 hE hc with h | h | h
    · exact hne h
    · exact key e16Orbits422 swap_mem_e16Orbits422 (exists_conj_of_orbitSizes_eq
        isElemAb2_e16Orbits422 card_e16Orbits422 hE hc (orbitSizesOf_e16Orbits422.trans h.symm))
    · exact key e16Orbits2222 swap_mem_e16Orbits2222 (exists_conj_of_orbitSizes_eq
        isElemAb2_e16Orbits2222 card_e16Orbits2222 hE hc (orbitSizesOf_e16Orbits2222.trans h.symm))
  · intro h
    obtain ⟨g, hg⟩ := exists_conj_of_orbitSizes_eq isElemAb2_e16Orbits44 card_e16Orbits44 hE hc
      (orbitSizesOf_e16Orbits44.trans h.symm)
    rw [← hg]
    rintro _ ⟨y, hy, rfl⟩
    exact Perm.mem_alternatingGroup.mpr
      ((E16Orbits.sign_conj_eq g y).trans (Perm.mem_alternatingGroup.mp
        (e16Orbits44_le_alternatingGroup hy)))

theorem ncard_cycleType_two_four_of_e16 {E : Subgroup (Perm (Fin 8))} (hE : IsElemAb2 E)
    (hc : Nat.card E = 16) :
    (orbitSizesOf E = {4, 4} →
      Set.ncard {x : Perm (Fin 8) | x ∈ E ∧ x.cycleType = {2, 2, 2, 2}} = 9) ∧
    (orbitSizesOf E = {4, 2, 2} →
      Set.ncard {x : Perm (Fin 8) | x ∈ E ∧ x.cycleType = {2, 2, 2, 2}} = 3) ∧
    (orbitSizesOf E = {2, 2, 2, 2} →
      Set.ncard {x : Perm (Fin 8) | x ∈ E ∧ x.cycleType = {2, 2, 2, 2}} = 1) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨g, hg⟩ := exists_conj_of_orbitSizes_eq isElemAb2_e16Orbits44 card_e16Orbits44 hE hc
      (orbitSizesOf_e16Orbits44.trans h.symm)
    rw [← hg, E16Orbits.ncard_cycleType_map_conj]
    exact ncard_cycleType_e16Orbits44
  · obtain ⟨g, hg⟩ := exists_conj_of_orbitSizes_eq isElemAb2_e16Orbits422 card_e16Orbits422 hE hc
      (orbitSizesOf_e16Orbits422.trans h.symm)
    rw [← hg, E16Orbits.ncard_cycleType_map_conj]
    exact ncard_cycleType_e16Orbits422
  · obtain ⟨g, hg⟩ := exists_conj_of_orbitSizes_eq isElemAb2_e16Orbits2222 card_e16Orbits2222 hE hc
      (orbitSizesOf_e16Orbits2222.trans h.symm)
    rw [← hg, E16Orbits.ncard_cycleType_map_conj]
    exact ncard_cycleType_e16Orbits2222

end CFSG.ASVolI.ChH
