module

public import CFSG.Quasithin.AppendixH.H9.H93.S8Struct.OrbitFixed
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.ASVolI.ChH

namespace ElemAb2Orbits

open Equiv

variable {E : Subgroup (Perm (Fin 8))}

theorem sum_orbitSizesOf (B : Subgroup (Perm (Fin 8))) : (orbitSizesOf B).sum = 8 := by
  classical
  have key := Finset.card_eq_sum_card_image (fun i : Fin 8 => (MulAction.orbit B i : Set (Fin 8)))
    Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at key
  refine Eq.trans ?_ key.symm
  refine Finset.sum_congr rfl fun O hO => ?_
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hO
  calc (MulAction.orbit B i : Set (Fin 8)).ncard
      = ((Finset.univ.filter fun x : Fin 8 =>
          (MulAction.orbit B x : Set (Fin 8)) = MulAction.orbit B i : Finset (Fin 8)) :
          Set (Fin 8)).ncard := by
        congr 1
        ext x
        simp [MulAction.orbit_eq_iff]
    _ = _ := Set.ncard_coe_finset _

theorem ncard_orbit_mem_orbitSizesOf (B : Subgroup (Perm (Fin 8))) (x : Fin 8) :
    (MulAction.orbit B x : Set (Fin 8)).ncard ∈ orbitSizesOf B := by
  classical
  exact Multiset.mem_map.mpr ⟨MulAction.orbit B x,
    Finset.mem_val.mpr (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩), rfl⟩

theorem exists_orbit_of_mem_orbitSizesOf {B : Subgroup (Perm (Fin 8))} {a : ℕ}
    (ha : a ∈ orbitSizesOf B) : ∃ x : Fin 8, (MulAction.orbit B x : Set (Fin 8)).ncard = a := by
  classical
  obtain ⟨O, hO, rfl⟩ := Multiset.mem_map.mp ha
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_val.mp hO)
  exact ⟨i, rfl⟩

theorem mem_orbitSizesOf_cases (hE : IsElemAb2 E) {a : ℕ} (ha : a ∈ orbitSizesOf E) :
    a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 8 := by
  obtain ⟨x, rfl⟩ := exists_orbit_of_mem_orbitSizesOf ha
  exact ncard_orbit_cases hE x

open Classical in
private noncomputable def orbitFinset (B : Subgroup (Perm (Fin 8))) : Finset (Set (Fin 8)) :=
  Finset.univ.image fun i : Fin 8 => (MulAction.orbit B i : Set (Fin 8))

private theorem orbitSizesOf_eq (B : Subgroup (Perm (Fin 8))) :
    orbitSizesOf B = (orbitFinset B).val.map Set.ncard := rfl

private theorem mem_orbitFinset {B : Subgroup (Perm (Fin 8))} {O : Set (Fin 8)} :
    O ∈ orbitFinset B ↔ ∃ i : Fin 8, MulAction.orbit B i = O := by
  classical
  simp [orbitFinset]

private noncomputable def orbitRep (B : Subgroup (Perm (Fin 8))) (O : Set (Fin 8)) : Fin 8 :=
  Function.invFun (fun i : Fin 8 => (MulAction.orbit B i : Set (Fin 8))) O

private theorem orbit_orbitRep {B : Subgroup (Perm (Fin 8))} {O : Set (Fin 8)}
    (hO : O ∈ orbitFinset B) : MulAction.orbit B (orbitRep B O) = O :=
  Function.invFun_eq (f := fun i : Fin 8 => (MulAction.orbit B i : Set (Fin 8)))
    (mem_orbitFinset.mp hO)

private noncomputable def evalReps (B : Subgroup (Perm (Fin 8))) (e : B)
    (O : orbitFinset B) : (O : Set (Fin 8)) :=
  ⟨e • orbitRep B O.1, (orbit_orbitRep O.2).subset (MulAction.mem_orbit _ e)⟩

private theorem evalReps_injective (hE : IsElemAb2 E) : Function.Injective (evalReps E) := by
  intro e e' h
  have key : ∀ O : orbitFinset E, (e : Perm (Fin 8)) (orbitRep E O.1) =
      (e' : Perm (Fin 8)) (orbitRep E O.1) := fun O => congrArg Subtype.val (congrFun h O)
  refine Subtype.ext (Equiv.ext fun x => ?_)
  have hO : (MulAction.orbit E x : Set (Fin 8)) ∈ orbitFinset E := mem_orbitFinset.mpr ⟨x, rfl⟩
  have hx : x ∈ MulAction.orbit E (orbitRep E (MulAction.orbit E x)) := by
    rw [orbit_orbitRep hO]
    exact MulAction.mem_orbit_self x
  obtain ⟨⟨g, hg⟩, hgx⟩ := MulAction.mem_orbit_iff.mp hx
  have hgx' : g (orbitRep E (MulAction.orbit E x)) = x := hgx
  rw [← hgx', apply_comm_of_isElemAb2 hE e.2 hg, apply_comm_of_isElemAb2 hE e'.2 hg,
    key ⟨_, hO⟩]

private theorem natCard_pi_eq :
    Nat.card (∀ O : orbitFinset E, (O : Set (Fin 8))) = (orbitSizesOf E).prod := by
  rw [Nat.card_pi, orbitSizesOf_eq, ← Finset.prod_eq_multiset_prod]
  simp only [Nat.card_coe_set_eq]
  exact Finset.prod_coe_sort (orbitFinset E) Set.ncard

theorem card_le_prod_orbitSizesOf (hE : IsElemAb2 E) : Nat.card E ≤ (orbitSizesOf E).prod := by
  rw [← natCard_pi_eq]
  exact Nat.card_le_card_of_injective _ (evalReps_injective hE)

theorem exists_mem_agree_on_orbit_reps (hE : IsElemAb2 E)
    (hle : (orbitSizesOf E).prod ≤ Nat.card E) {σ : Perm (Fin 8)}
    (hσ : ∀ x, σ x ∈ MulAction.orbit E x) :
    ∃ e ∈ E, ∀ x, ∃ ρ ∈ MulAction.orbit E x, e ρ = σ ρ := by
  have hbij : Function.Bijective (evalReps E) :=
    (evalReps_injective hE).bijective_of_nat_card_le (by rw [natCard_pi_eq]; exact hle)
  let y : ∀ O : orbitFinset E, (O : Set (Fin 8)) :=
    fun O => ⟨σ (orbitRep E O.1), (orbit_orbitRep O.2).subset (hσ _)⟩
  obtain ⟨e, he⟩ := hbij.2 y
  refine ⟨e.1, e.2, fun x => ?_⟩
  have hO : (MulAction.orbit E x : Set (Fin 8)) ∈ orbitFinset E := mem_orbitFinset.mpr ⟨x, rfl⟩
  refine ⟨orbitRep E (MulAction.orbit E x), ?_, congrArg Subtype.val (congrFun he ⟨_, hO⟩)⟩
  have := MulAction.mem_orbit_self (M := E) (orbitRep E (MulAction.orbit E x))
  rwa [orbit_orbitRep hO] at this

end ElemAb2Orbits

end CFSG.ASVolI.ChH
