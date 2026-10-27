module

public import CFSG.Quasithin.AppendixH.H9.H93.S8Struct.OrbitBound
public import CFSG.Quasithin.AppendixH.H9.H93.S8Struct.OrbitLocal
public import CFSG.Quasithin.AppendixH.H9.H93.S8Struct.OrbitSizeArith

public section

namespace CFSG.ASVolI.ChH

open Equiv ElemAb2Orbits

private theorem prod_orbitSizesOf_le {E : Subgroup (Perm (Fin 8))} (hE : IsElemAb2 E) :
    (orbitSizesOf E).prod ≤ 16 :=
  multiset_prod_le_sixteen (fun _ ha => mem_orbitSizesOf_cases hE ha) (sum_orbitSizesOf E)

theorem card_le_sixteen_of_isElemAb2 {E : Subgroup (Perm (Fin 8))} (hE : IsElemAb2 E) :
    Nat.card E ≤ 16 :=
  (card_le_prod_orbitSizesOf hE).trans (prod_orbitSizesOf_le hE)

theorem orbitSizes_of_e16 {E : Subgroup (Perm (Fin 8))} (hE : IsElemAb2 E)
    (hc : Nat.card E = 16) :
    orbitSizesOf E = {4, 4} ∨ orbitSizesOf E = {4, 2, 2} ∨ orbitSizesOf E = {2, 2, 2, 2} :=
  multiset_eq_of_sixteen_le_prod (fun _ ha => mem_orbitSizesOf_cases hE ha) (sum_orbitSizesOf E)
    (by rw [← hc]; exact card_le_prod_orbitSizesOf hE)

theorem ncard_orbit_of_e16 {E : Subgroup (Perm (Fin 8))} (hE : IsElemAb2 E)
    (hc : Nat.card E = 16) (x : Fin 8) :
    Set.ncard (MulAction.orbit E x) = 2 ∨ Set.ncard (MulAction.orbit E x) = 4 := by
  have hx := ncard_orbit_mem_orbitSizesOf E x
  rcases orbitSizes_of_e16 hE hc with hs | hs | hs <;> rw [hs] at hx <;> simp at hx <;> omega

theorem mem_e16_iff {E : Subgroup (Perm (Fin 8))} (hE : IsElemAb2 E) (hc : Nat.card E = 16)
    (σ : Perm (Fin 8)) :
    σ ∈ E ↔ ∀ x : Fin 8, (∀ y ∈ MulAction.orbit E x, σ y ∈ MulAction.orbit E x) ∧
      ((∀ y ∈ MulAction.orbit E x, σ y = y) ∨
        ∀ y ∈ MulAction.orbit E x, σ y ≠ y ∧ σ (σ y) = y) := by
  constructor
  · intro hσ x
    exact orbit_local_of_mem hE hσ x
  · intro h
    have hσ : ∀ x, σ x ∈ MulAction.orbit E x := fun x => (h x).1 x (MulAction.mem_orbit_self x)
    obtain ⟨e, he, hag⟩ := exists_mem_agree_on_orbit_reps hE
      (by rw [hc]; exact prod_orbitSizesOf_le hE) hσ
    suffices hσe : σ = e by rw [hσe]; exact he
    refine Equiv.ext fun x => ?_
    obtain ⟨ρ, hρ, hρe⟩ := hag x
    have hcard : (MulAction.orbit E x : Set (Fin 8)).ncard ≤ 4 := by
      rcases ncard_orbit_of_e16 hE hc x with hn | hn <;> omega
    exact perm_apply_eq_of_local hcard (h x).1 (orbit_local_of_mem hE he x).1 (h x).2
      (orbit_local_of_mem hE he x).2 hρ hρe.symm x (MulAction.mem_orbit_self x)

end CFSG.ASVolI.ChH
