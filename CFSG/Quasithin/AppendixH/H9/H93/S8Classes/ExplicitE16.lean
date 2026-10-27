module

public import CFSG.Quasithin.AppendixH.H9.H93.S8Defs
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ASVolI.ChH

open Equiv

private def goodList (L : List (Perm (Fin 8))) : Bool :=
  L.contains 1 && L.all fun a =>
    L.contains a⁻¹ && (a * a == 1) && L.all fun b => L.contains (a * b) && (a * b == b * a)

private theorem goodList_spec {L : List (Perm (Fin 8))} (h : goodList L = true) :
    (1 : Perm (Fin 8)) ∈ L ∧ (∀ a ∈ L, a⁻¹ ∈ L) ∧ (∀ a ∈ L, a * a = 1) ∧
      (∀ a ∈ L, ∀ b ∈ L, a * b ∈ L) ∧ (∀ a ∈ L, ∀ b ∈ L, a * b = b * a) := by
  simp only [goodList, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun a ha => (h2 a ha).1.1, fun a ha => (h2 a ha).1.2, fun a ha b hb => ?_,
    fun a ha b hb => ?_⟩
  · exact ((h2 a ha).2 b hb).1
  · exact ((h2 a ha).2 b hb).2

private def listSubgroup (L : List (Perm (Fin 8))) (h : goodList L = true) :
    Subgroup (Perm (Fin 8)) where
  carrier := {x | x ∈ L}
  mul_mem' := fun {a b} ha hb => (goodList_spec h).2.2.2.1 a ha b hb
  one_mem' := (goodList_spec h).1
  inv_mem' := fun {a} ha => (goodList_spec h).2.1 a ha

private theorem mem_listSubgroup {L : List (Perm (Fin 8))} {h : goodList L = true}
    {x : Perm (Fin 8)} : x ∈ listSubgroup L h ↔ x ∈ L := Iff.rfl

private theorem isElemAb2_listSubgroup {L : List (Perm (Fin 8))} (h : goodList L = true) :
    IsElemAb2 (listSubgroup L h) := by
  refine ⟨fun a ha b hb => (goodList_spec h).2.2.2.2 a ha b hb, fun a ha => ?_⟩
  rw [sq]
  exact (goodList_spec h).2.2.1 a ha

private theorem card_listSubgroup {L : List (Perm (Fin 8))} (h : goodList L = true) :
    Nat.card (listSubgroup L h) = L.toFinset.card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [mem_listSubgroup])

private theorem orbit_listSubgroup {L : List (Perm (Fin 8))} (h : goodList L = true) (x : Fin 8) :
    MulAction.orbit (listSubgroup L h) x = ↑((L.map fun g => g x).toFinset) := by
  ext y
  simp only [MulAction.mem_orbit_iff, Finset.mem_coe, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

private theorem orbitSizesOf_eq_of_orbit_eq_coe (B : Subgroup (Perm (Fin 8)))
    (T : Fin 8 → Finset (Fin 8)) (hT : ∀ x, MulAction.orbit B x = ↑(T x)) :
    orbitSizesOf B = (Finset.univ.image T).val.map Finset.card := by
  classical
  unfold orbitSizesOf
  have himg : (Finset.univ.image fun i : Fin 8 => (MulAction.orbit B i : Set (Fin 8))) =
      (Finset.univ.image T).image (fun F : Finset (Fin 8) => (F : Set (Fin 8))) := by
    rw [Finset.image_image]
    exact Finset.image_congr fun i _ => hT i
  rw [himg, Finset.image_val_of_injOn Finset.coe_injective.injOn, Multiset.map_map]
  exact Multiset.map_congr rfl fun F _ => Set.ncard_coe_finset F

private theorem cycleType_eq_two_four_iff {σ : Perm (Fin 8)} (h : σ * σ = 1) :
    σ.cycleType = {2, 2, 2, 2} ↔ ∀ i, σ i ≠ i := by
  constructor
  · intro hc i
    have hsum := Equiv.Perm.sum_cycleType σ
    rw [hc] at hsum
    have h8 : σ.support.card = 8 := by simpa using hsum.symm
    have hsupp : σ.support = Finset.univ :=
      Finset.eq_univ_of_card σ.support (by simpa using h8)
    exact Equiv.Perm.mem_support.mp (hsupp ▸ Finset.mem_univ i)
  · intro hf
    have hsupp : σ.support = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr fun i => Equiv.Perm.mem_support.mpr (hf i)
    have hsum : σ.cycleType.sum = 8 := by
      rw [Equiv.Perm.sum_cycleType, hsupp]
      simp
    have hord : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
    have hall : ∀ n ∈ σ.cycleType, n = 2 := fun n hn =>
      le_antisymm (Nat.le_of_dvd two_pos ((Equiv.Perm.dvd_of_mem_cycleType hn).trans hord))
        (Equiv.Perm.two_le_of_mem_cycleType hn)
    have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
      Multiset.eq_replicate_card.2 hall
    have hcard : Multiset.card σ.cycleType = 4 := by
      have := congrArg Multiset.sum hrep
      rw [Multiset.sum_replicate, hsum] at this
      simp at this
      omega
    rw [hrep, hcard]
    rfl

private theorem ncard_cycleType_two_four_listSubgroup {L : List (Perm (Fin 8))}
    (h : goodList L = true) :
    Set.ncard {x : Perm (Fin 8) | x ∈ listSubgroup L h ∧ x.cycleType = {2, 2, 2, 2}} =
      (L.toFinset.filter fun x => ∀ i, x i ≠ i).card := by
  have hs : {x : Perm (Fin 8) | x ∈ listSubgroup L h ∧ x.cycleType = {2, 2, 2, 2}} =
      ↑(L.toFinset.filter fun x => ∀ i, x i ≠ i) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.coe_filter, List.mem_toFinset, mem_listSubgroup]
    constructor
    · rintro ⟨hx, hc⟩
      exact ⟨hx, (cycleType_eq_two_four_iff ((goodList_spec h).2.2.1 x hx)).1 hc⟩
    · rintro ⟨hx, hf⟩
      exact ⟨hx, (cycleType_eq_two_four_iff ((goodList_spec h).2.2.1 x hx)).2 hf⟩
  rw [hs, Set.ncard_coe_finset]

private def kleinList (a b c d : Fin 8) : List (Perm (Fin 8)) :=
  [1, swap a b * swap c d, swap a c * swap b d, swap a d * swap b c]

private def pairList (a b : Fin 8) : List (Perm (Fin 8)) := [1, swap a b]

private def mulList (A B : List (Perm (Fin 8))) : List (Perm (Fin 8)) :=
  A.flatMap fun x => B.map (x * ·)

private def list44 : List (Perm (Fin 8)) := mulList (kleinList 0 1 2 3) (kleinList 4 5 6 7)

private def list422 : List (Perm (Fin 8)) :=
  mulList (mulList (kleinList 0 1 2 3) (pairList 4 5)) (pairList 6 7)

private def list2222 : List (Perm (Fin 8)) :=
  mulList (mulList (mulList (pairList 0 1) (pairList 2 3)) (pairList 4 5)) (pairList 6 7)

private theorem good44 : goodList list44 = true := by decide +kernel
private theorem good422 : goodList list422 = true := by decide +kernel
private theorem good2222 : goodList list2222 = true := by decide +kernel

def e16Orbits44 : Subgroup (Perm (Fin 8)) := listSubgroup list44 good44

def e16Orbits422 : Subgroup (Perm (Fin 8)) := listSubgroup list422 good422

def e16Orbits2222 : Subgroup (Perm (Fin 8)) := listSubgroup list2222 good2222

theorem isElemAb2_e16Orbits44 : IsElemAb2 e16Orbits44 := isElemAb2_listSubgroup good44
theorem isElemAb2_e16Orbits422 : IsElemAb2 e16Orbits422 := isElemAb2_listSubgroup good422
theorem isElemAb2_e16Orbits2222 : IsElemAb2 e16Orbits2222 := isElemAb2_listSubgroup good2222

theorem card_e16Orbits44 : Nat.card e16Orbits44 = 16 := by
  rw [e16Orbits44, card_listSubgroup]
  decide +kernel

theorem card_e16Orbits422 : Nat.card e16Orbits422 = 16 := by
  rw [e16Orbits422, card_listSubgroup]
  decide +kernel

theorem card_e16Orbits2222 : Nat.card e16Orbits2222 = 16 := by
  rw [e16Orbits2222, card_listSubgroup]
  decide +kernel

theorem orbitSizesOf_e16Orbits44 : orbitSizesOf e16Orbits44 = {4, 4} := by
  rw [e16Orbits44, orbitSizesOf_eq_of_orbit_eq_coe _ _ (orbit_listSubgroup good44)]
  decide +kernel

theorem orbitSizesOf_e16Orbits422 : orbitSizesOf e16Orbits422 = {4, 2, 2} := by
  rw [e16Orbits422, orbitSizesOf_eq_of_orbit_eq_coe _ _ (orbit_listSubgroup good422)]
  decide +kernel

theorem orbitSizesOf_e16Orbits2222 : orbitSizesOf e16Orbits2222 = {2, 2, 2, 2} := by
  rw [e16Orbits2222, orbitSizesOf_eq_of_orbit_eq_coe _ _ (orbit_listSubgroup good2222)]
  decide +kernel

theorem e16Orbits44_le_alternatingGroup : e16Orbits44 ≤ alternatingGroup (Fin 8) := by
  have h : list44.all (fun x => decide (Perm.sign x = 1)) = true := by decide +kernel
  intro x hx
  rw [Perm.mem_alternatingGroup]
  have := List.all_eq_true.mp h x hx
  simpa using this

theorem swap_mem_e16Orbits422 : swap (4 : Fin 8) 5 ∈ e16Orbits422 := by
  show swap (4 : Fin 8) 5 ∈ list422
  decide +kernel

theorem swap_mem_e16Orbits2222 : swap (4 : Fin 8) 5 ∈ e16Orbits2222 := by
  show swap (4 : Fin 8) 5 ∈ list2222
  decide +kernel

theorem ncard_cycleType_e16Orbits44 :
    Set.ncard {x : Perm (Fin 8) | x ∈ e16Orbits44 ∧ x.cycleType = {2, 2, 2, 2}} = 9 := by
  rw [e16Orbits44, ncard_cycleType_two_four_listSubgroup]
  decide +kernel

theorem ncard_cycleType_e16Orbits422 :
    Set.ncard {x : Perm (Fin 8) | x ∈ e16Orbits422 ∧ x.cycleType = {2, 2, 2, 2}} = 3 := by
  rw [e16Orbits422, ncard_cycleType_two_four_listSubgroup]
  decide +kernel

theorem ncard_cycleType_e16Orbits2222 :
    Set.ncard {x : Perm (Fin 8) | x ∈ e16Orbits2222 ∧ x.cycleType = {2, 2, 2, 2}} = 1 := by
  rw [e16Orbits2222, ncard_cycleType_two_four_listSubgroup]
  decide +kernel

end CFSG.ASVolI.ChH
