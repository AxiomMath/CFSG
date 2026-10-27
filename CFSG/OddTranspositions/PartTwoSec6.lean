module

public import CFSG.Timmesfeld.Bridge.OddLocalDefs

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type*} [Group G]

@[expose] def perpMem (D : Set G) (u : G) : Set G := {w | w ∈ D ∧ Commute w u}

@[expose] def Vmem (D : Set G) (u : G) : Set G := {v | v ∈ D ∧ perpMem D v = perpMem D u}

@[expose] def Wmem (D : Set G) (u : G) : Set G :=
  {v | v ∈ D ∧ commSet D v = commSet D u}

theorem mem_perpMem {D : Set G} {u w : G} : w ∈ perpMem D u ↔ w ∈ D ∧ Commute w u := Iff.rfl

theorem mem_Vmem {D : Set G} {u v : G} :
    v ∈ Vmem D u ↔ v ∈ D ∧ perpMem D v = perpMem D u := Iff.rfl

theorem mem_Wmem {D : Set G} {u w : G} :
    w ∈ Wmem D u ↔ w ∈ D ∧ commSet D w = commSet D u := Iff.rfl

theorem mem_perpMem_self {D : Set G} {u : G} (hu : u ∈ D) : u ∈ perpMem D u :=
  ⟨hu, Commute.refl u⟩

theorem mem_Vmem_self {D : Set G} {u : G} (hu : u ∈ D) : u ∈ Vmem D u :=
  ⟨hu, rfl⟩

theorem not_odd_orderOf_of_eq_mul_mem_normal {N : Subgroup G} (hN : N.Normal)
    (hNo : Odd (Nat.card N)) {n x y : G} (hn : n ∈ N) (hy : y = n * x)
    (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) : ¬ Odd (orderOf y) := by
  haveI : N.Normal := hN
  have hxN : x ∉ N := by
    intro hxmem
    exact hNo.ne_two_of_dvd_nat (Subgroup.orderOf_dvd_natCard N hxmem)
      (orderOf_eq_prime hx2 hx1)
  have hφx : orderOf (QuotientGroup.mk' N x) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, hx2, map_one]
    · intro h
      exact hxN ((QuotientGroup.eq_one_iff x).mp (by simpa using h))
  have hφy : QuotientGroup.mk' N y = QuotientGroup.mk' N x := by
    rw [hy, map_mul]
    have hn1 : QuotientGroup.mk' N n = 1 := by
      simpa using (QuotientGroup.eq_one_iff n).mpr hn
    rw [hn1, one_mul]
  have hdvd : 2 ∣ orderOf y := by
    have h := orderOf_map_dvd (QuotientGroup.mk' N) y
    rwa [hφy, hφx] at h
  intro hOdd
  exact (hOdd.ne_two_of_dvd_nat hdvd) rfl

theorem commSet_eq_of_mem_mul_normal {D : Set G} (hodd : Asc72.IsOddTransp D)
    {N : Subgroup G} (hN : N.Normal) (hNo : Odd (Nat.card N))
    {u w : G} (hu : u ∈ D) (hw : w ∈ D) {n : G} (hn : n ∈ N) (hwu : w = n * u) :
    commSet D w = commSet D u := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvD, hvw, hvne⟩ := hv
    have hv2 : v * v = 1 := hodd.mul_self_eq_one hvD
    have hw2 : w * w = 1 := hodd.mul_self_eq_one hw
    have hu2 : u * u = 1 := hodd.mul_self_eq_one hu
    have hx2 : (v * w) ^ 2 = 1 := (commute_iff_mul_sq_eq_one hv2 hw2).1 hvw
    have hx1 : v * w ≠ 1 := fun h => hvne (hodd.eq_of_mul_eq_one hvD h)
    have hvu_eq : v * u = (v * n⁻¹ * v⁻¹) * (v * w) := by
      rw [hwu]
      group
    have hn' : v * n⁻¹ * v⁻¹ ∈ N := hN.conj_mem n⁻¹ (N.inv_mem hn) v
    have hnotodd :=
      not_odd_orderOf_of_eq_mul_mem_normal hN hNo hn' hvu_eq hx2 hx1
    have hdvd : orderOf (v * u) ∣ 2 := (hodd.2 v hvD u hu).resolve_right hnotodd
    have hsq : (v * u) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
    have hvu : Commute v u := (commute_iff_mul_sq_eq_one hv2 hu2).2 hsq
    have hne : v ≠ u := by
      intro h
      have hwu' : w * u = n := by rw [hwu, mul_assoc, hu2, mul_one]
      have hwne : w ≠ u := fun h' => hvne (h.trans h'.symm)
      have hcomm : Commute w u := by
        rw [← h]
        exact hvw.symm
      have hn2 : orderOf n = 2 := by
        rw [← hwu']
        exact hodd.orderOf_mul_eq_two hw hu hwne hcomm
      exact hNo.ne_two_of_dvd_nat (Subgroup.orderOf_dvd_natCard N hn) hn2
    exact ⟨hvD, hvu, hne⟩
  · intro hv
    obtain ⟨hvD, hvu, hvne⟩ := hv
    have hv2 : v * v = 1 := hodd.mul_self_eq_one hvD
    have hu2 : u * u = 1 := hodd.mul_self_eq_one hu
    have hx2 : (v * u) ^ 2 = 1 := (commute_iff_mul_sq_eq_one hv2 hu2).1 hvu
    have hx1 : v * u ≠ 1 := fun h => hvne (hodd.eq_of_mul_eq_one hvD h)
    have hvw_eq : v * w = (v * n * v⁻¹) * (v * u) := by
      rw [hwu]
      group
    have hn' : v * n * v⁻¹ ∈ N := hN.conj_mem n hn v
    have hnotodd :=
      not_odd_orderOf_of_eq_mul_mem_normal hN hNo hn' hvw_eq hx2 hx1
    have hdvd : orderOf (v * w) ∣ 2 := (hodd.2 v hvD w hw).resolve_right hnotodd
    have hsq : (v * w) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
    have hvw : Commute v w := (commute_iff_mul_sq_eq_one hv2 (hodd.mul_self_eq_one hw)).2 hsq
    have hne : v ≠ w := by
      intro h
      have hnu : v * u = n := by rw [h, hwu, mul_assoc, hu2, mul_one]
      have hn2 : orderOf n = 2 := by
        rw [← hnu]
        exact hodd.orderOf_mul_eq_two hvD hu hvne hvu
      exact hNo.ne_two_of_dvd_nat (Subgroup.orderOf_dvd_natCard N hn) hn2
    exact ⟨hvD, hvw, hne⟩

theorem mem_Wmem_of_mem_mul_normal {D : Set G} (hodd : Asc72.IsOddTransp D)
    {N : Subgroup G} (hN : N.Normal) (hNo : Odd (Nat.card N))
    {u w n : G} (hu : u ∈ D) (hw : w ∈ D) (hn : n ∈ N) (hwu : w = n * u) :
    w ∈ Wmem D u :=
  ⟨hw, commSet_eq_of_mem_mul_normal hodd hN hNo hu hw hn hwu⟩

end CFSG.OddTranspositions
