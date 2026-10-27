module

public import CFSG.Monster.Existence.BabyTableIVOf
public import CFSG.Monster.GMS.Facts.BabyFi22

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.GMS CFSG.Blueprint

theorem babyOrbit_of_mem_labelSphere
    {r t : NativeSporadic.B} {v u : CVert}
    (hv : clabelS v = babyToShat r) (hu : clabelS u = babyToShat t) {k : Fin 4}
    (h : u ∈ labelSphere k v) : BabyOrbit k r t := by
  have hmul : babyToShat (r * t) = clabelS v * clabelS u := by rw [map_mul, hv, hu]
  match k, h with
  | 0, h =>
    change BabyInv 1 (r * t)
    have h1 : IsConj (babyToShat (babyRep 0)) (babyToShat (r * t)) := by
      rw [babyToShat_babyRep_zero, hmul]
      exact (isConj_clabelS_mul_of_mem_zero h).symm
    exact babyInv_one_babyRep_zero.of_isConj (isConj_babyToShat_iff.1 h1)
  | 1, h =>
    change BabyInv 3 (r * t)
    have h1 : IsConj (babyToShat (babyRep 5)) (babyToShat (r * t)) := by
      rw [babyToShat_babyRep, hmul]
      exact (isConj_clabelS_mul_of_mem_one h).symm
    exact babyInv_three_babyRep_five.of_isConj (isConj_babyToShat_iff.1 h1)
  | 2, h =>
    change orderOf (r * t) = 3
    have e : orderOf (babyToShat (r * t)) = 3 := by
      rw [hmul]
      exact orderOf_clabelS_mul_of_mem_two h
    rwa [MulEquiv.orderOf_eq] at e
  | 3, h =>
    change orderOf (r * t) = 4 ∧ BabyInv 1 ((r * t) ^ 2)
    refine ⟨?_, ?_⟩
    · have e : orderOf (babyToShat (r * t)) = 4 := by
        rw [hmul]
        exact orderOf_clabelS_mul_of_mem_three h
      rwa [MulEquiv.orderOf_eq] at e
    · have h1 : IsConj (babyToShat (babyRep 0)) (babyToShat ((r * t) ^ 2)) := by
        rw [babyToShat_babyRep_zero, map_pow, hmul]
        exact (isConj_sq_clabelS_mul_of_mem_three h).symm
      exact babyInv_one_babyRep_zero.of_isConj (isConj_babyToShat_iff.1 h1)

theorem babyOrbit_iff_mem_labelSphere
    {r t : NativeSporadic.B} {v u : CVert} (hr : BabyInv 0 r)
    (hv : clabelS v = babyToShat r) (hu : clabelS u = babyToShat t) (k : Fin 4) :
    BabyOrbit k r t ↔ u ∈ labelSphere k v := by
  refine ⟨fun h => ?_, babyOrbit_of_mem_labelSphere hv hu⟩
  rcases labelSphere_cover v u with rfl | ⟨j, hj⟩
  · have e : t = r := babyToShat.injective (hu.symm.trans hv)
    subst e
    exact absurd h (not_babyOrbit_self hr)
  · exact babyOrbit_unique h (babyOrbit_of_mem_labelSphere hv hu hj) ▸ hj

theorem mem_babyStar_iff
    {r s t : NativeSporadic.B} {v w u : CVert} (hr : BabyInv 0 r)
    (hs : BabyInv 0 s) (ht : BabyInv 0 t) (hv : clabelS v = babyToShat r)
    (hw : clabelS w = babyToShat s) (hu : clabelS u = babyToShat t) :
    t ∈ babyStar r s ↔ u ∈ cgraph.commonNeighbors v w := by
  have h1 := babyOrbit_iff_mem_labelSphere hr hv hu 0
  have h2 := babyOrbit_iff_mem_labelSphere hs hw hu 0
  change (BabyInv 0 t ∧ BabyOrbit 0 r t ∧ BabyOrbit 0 s t) ↔ _
  rw [h1, h2, SimpleGraph.mem_commonNeighbors]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨ht, h.1, h.2⟩⟩

theorem image_babyStar_eq
    (hcls : ∀ t : NativeSporadic.B, BabyInv 0 t → IsConj t (babyRep 1))
    {r s : NativeSporadic.B} {v w : CVert} (hr : BabyInv 0 r) (hs : BabyInv 0 s)
    (hv : clabelS v = babyToShat r) (hw : clabelS w = babyToShat s) :
    babyToShat '' babyStar r s = clabelS '' cgraph.commonNeighbors v w := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨u, hu⟩ := (babyInv_zero_iff_clabelS hcls t).1 ht.1
    exact ⟨u, (mem_babyStar_iff hr hs ht.1 hv hw hu).1 ht, hu⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t, clabelS u = babyToShat t := ⟨babyToShat.symm (clabelS u), by simp⟩
    have ht0 : BabyInv 0 t := (babyInv_zero_iff_clabelS hcls t).2 ⟨u, ht⟩
    exact ⟨t, (mem_babyStar_iff hr hs ht0 hv hw ht).2 hu, ht.symm⟩

end CFSG.Monster.Existence
