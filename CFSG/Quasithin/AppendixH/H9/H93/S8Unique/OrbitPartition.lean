module

public import CFSG.Quasithin.AppendixH.H9.H93.S8Defs
public import Mathlib.Tactic.Basify

public section

namespace CFSG.ASVolI.ChH

open Equiv

structure HasOrbitPartition (E : Subgroup (Perm (Fin 8))) (A : Finset (Fin 8)) : Prop where
  card_eq : A.card = 4
  orbit_of_mem : ∀ y ∈ A, MulAction.orbit E y = (A : Set (Fin 8))
  orbit_of_notMem : ∀ y ∉ A, MulAction.orbit E y = ((Aᶜ : Finset (Fin 8)) : Set (Fin 8))

theorem ncard_orbit_eq_four_of_orbitSizesOf_eq {E : Subgroup (Perm (Fin 8))}
    (h : orbitSizesOf E = {4, 4}) (x : Fin 8) : Set.ncard (MulAction.orbit E x) = 4 := by
  have hmem : Set.ncard (MulAction.orbit E x) ∈ orbitSizesOf E :=
    Multiset.mem_map.mpr ⟨_, Finset.mem_val.mpr
      (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩), rfl⟩
  rw [h] at hmem
  simpa using hmem

theorem exists_hasOrbitPartition_of_orbitSizesOf_eq {E : Subgroup (Perm (Fin 8))}
    (h : orbitSizesOf E = {4, 4}) :
    ∃ A : Finset (Fin 8), (0 : Fin 8) ∈ A ∧ HasOrbitPartition E A := by
  have hn := ncard_orbit_eq_four_of_orbitSizesOf_eq h
  have hfin : (MulAction.orbit E (0 : Fin 8)).Finite := Set.toFinite _
  have hcard : hfin.toFinset.card = 4 := by
    rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
    exact hn 0
  refine ⟨hfin.toFinset, hfin.mem_toFinset.mpr (MulAction.mem_orbit_self _), hcard, ?_, ?_⟩
  · intro y hy
    rw [MulAction.orbit_eq_iff.mpr (hfin.mem_toFinset.mp hy), Set.Finite.coe_toFinset]
  · intro y hy
    have hy0 : y ∉ MulAction.orbit E (0 : Fin 8) := fun h' => hy (hfin.mem_toFinset.mpr h')
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · intro z hz
      rw [Finset.mem_coe, Finset.mem_compl, hfin.mem_toFinset]
      intro hz0
      apply hy0
      have e1 : MulAction.orbit E z = MulAction.orbit E 0 := MulAction.orbit_eq_iff.mpr hz0
      have e2 : MulAction.orbit E z = MulAction.orbit E y := MulAction.orbit_eq_iff.mpr hz
      exact (e2.symm.trans e1) ▸ MulAction.mem_orbit_self y
    · rw [Set.ncard_coe_finset, Finset.card_compl, hcard, hn y]
      simp

theorem HasOrbitPartition.compl {E : Subgroup (Perm (Fin 8))} {A : Finset (Fin 8)}
    (h : HasOrbitPartition E A) : HasOrbitPartition E Aᶜ where
  card_eq := by rw [Finset.card_compl, h.card_eq]; simp
  orbit_of_mem y hy := h.orbit_of_notMem y (Finset.mem_compl.mp hy)
  orbit_of_notMem y hy := by
    have hyA : y ∈ A := by simpa using hy
    rw [h.orbit_of_mem y hyA, compl_compl]

theorem HasOrbitPartition.orbit_eq {E E' : Subgroup (Perm (Fin 8))} {A : Finset (Fin 8)}
    (h : HasOrbitPartition E A) (h' : HasOrbitPartition E' A) (y : Fin 8) :
    MulAction.orbit E y = MulAction.orbit E' y := by
  by_cases hy : y ∈ A
  · rw [h.orbit_of_mem y hy, h'.orbit_of_mem y hy]
  · rw [h.orbit_of_notMem y hy, h'.orbit_of_notMem y hy]

end CFSG.ASVolI.ChH
