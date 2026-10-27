module

public import CFSG.Monster.B.TwoA.Fischer.AffineCayleyOrbits

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Generic
open scoped IsMulCommutative

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

theorem not_commute_conj_of_orderOf {L : Type*} [Group L] {t a : L} (ht : t * t = 1)
    (ha : a * a = 1) (h3 : orderOf (t * a) = 3) : ¬Commute t (a * t * a⁻¹) := by
  intro hc
  have h3' : (t * a) ^ 3 = 1 := by
    rw [← h3]
    exact pow_orderOf_eq_one _
  have hbraid := braid_of_pow_three_eq_one ht ha h3'
  rw [inv_eq_of_mul_eq_one_right ha, hbraid] at hc
  have h1 : t * (t * a * t) = a * t := by rw [← mul_assoc, ← mul_assoc, ht, one_mul]
  have h2 : t * a * t * t = t * a := by rw [mul_assoc, ht, mul_one]
  have hat : a * t = t * a := by
    have h := hc.eq
    rwa [h1, h2] at h
  exact not_commute_of_orderOf_mul_eq_three ht ha h3 hat.symm

theorem commute_conj_of_pow_four {L : Type*} [Group L] {t u : L} (ht : t * t = 1)
    (hu : u * u = 1) (h4 : (u * t) ^ 4 = 1) : Commute t (u * t * u⁻¹) := by
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have e1 : u * t * (u * t) * (u * t * (u * t)) = 1 := by
    rw [← h4]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have e2 : u * t * (u * t) = (u * t * (u * t))⁻¹ := eq_inv_of_mul_eq_one_left e1
  rw [mul_inv_rev, mul_inv_rev, hu', ht'] at e2
  rw [hu']
  change t * (u * t * u) = u * t * u * t
  calc t * (u * t * u) = t * u * (t * u) := by group
    _ = u * t * (u * t) := e2.symm
    _ = u * t * u * t := by group

theorem commute_conj_mul_of_pow_three {L : Type*} [Group L] {t a b : L} (ht : t * t = 1)
    (ha : a * a = 1) (hb : b * b = 1) (hab : Commute a b) (h3a : (t * a) ^ 3 = 1)
    (h3b : (t * b) ^ 3 = 1) : Commute t (a * b * t * (a * b)⁻¹) := by
  have h4 := pow_four_eq_one_of_braid ha hb ht hab.eq (braid_of_pow_three_eq_one ht ha h3a)
    (braid_of_pow_three_eq_one ht hb h3b)
  have hu : a * b * (a * b) = 1 := by
    rw [show a * b * (a * b) = a * (b * a) * b by group, ← hab.eq,
      show a * (a * b) * b = a * a * (b * b) by group, ha, hb, one_mul]
  exact commute_conj_of_pow_four ht hu h4

theorem act_act_eq_conj {k : S} {x : V} (hk : act k x = x) (r : S) :
    act k (act r x) = act (k * r * k⁻¹) x := by
  have hk' : act k⁻¹ x = x := by
    have h := act_inv_act (act := act) k x
    rwa [hk] at h
  rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hk']

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem lab_mul_self {y : V} (hy : y ∈ Y) : lab y * lab y = 1 :=
  mul_self_eq_one_of_orderOf_eq_two (hS.orderOf_lab y hy)

theorem orderOf_lab_mul_of_mem_omega {C : Set V} (hC : IsSliceMaxClique lab Y C) {x : V}
    (hx : x ∈ hexadFiber lab Y C ∅) {a : V} (ha : a ∈ C) : orderOf (lab x * lab a) = 3 := by
  refine hS.orderOf_mul x hx.1 a (hC.1.1 ha) fun hc => ?_
  have hne : x ≠ a := fun h => hx.2.1 (h ▸ ha)
  have hmem : a ∈ C ∩ (sliceGraph lab Y).neighborSet x := ⟨ha, hx.1, hC.1.1 ha, hne, hc⟩
  rw [hx.2.2] at hmem
  exact hmem

theorem pow_three_lab_mul_of_mem_omega {C : Set V} (hC : IsSliceMaxClique lab Y C) {x : V}
    (hx : x ∈ hexadFiber lab Y C ∅) {a : V} (ha : a ∈ C) : (lab x * lab a) ^ 3 = 1 := by
  rw [← hS.orderOf_lab_mul_of_mem_omega hC hx ha]
  exact pow_orderOf_eq_one _

theorem act_injOn {C : Set V} (hC : IsSliceMaxClique lab Y C) {x : V}
    (hx : x ∈ hexadFiber lab Y C ∅) : Set.InjOn (fun r => act r x) (ptStab act lab Y C) := by
  intro r hr s hs h
  have h1 : act (s⁻¹ * r) x = x := by
    simp only at h
    rw [map_mul, Equiv.Perm.mul_apply, h, act_inv_act]
  have h2 := hS.eq_one_of_act_eq hC hx
    ((ptStab act lab Y C).mul_mem ((ptStab act lab Y C).inv_mem hs) hr) h1
  rw [inv_mul_eq_one] at h2
  exact h2.symm

theorem image_neighborSet {a : S} (ha : a ∈ sliceGroup lab Y) (v : V) :
    act a '' (sliceGraph lab Y).neighborSet v = (sliceGraph lab Y).neighborSet (act a v) := by
  ext y
  rw [mem_image_act_iff, SimpleGraph.mem_neighborSet, SimpleGraph.mem_neighborSet,
    ← hS.adj_act_iff ha v (act a⁻¹ y), act_act_inv]

section Max

variable {C : Set V} (hC : IsSliceMaxClique lab Y C)
  [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
include hC

theorem not_adj_of_mem_labelLayer_three {x : V} (hx : x ∈ hexadFiber lab Y C ∅) {r : S}
    (hr : r ∈ labelLayer lab C 3) : ¬(sliceGraph lab Y).Adj x (act r x) := by
  intro hadj
  have hsub : (fun r' => act r' x) '' labelLayer lab C 3 ⊆ (sliceGraph lab Y).neighborSet x := by
    rintro _ ⟨r', hr', rfl⟩
    obtain ⟨k, hk, hkr⟩ := hS.exists_conj_eq_of_mem_labelLayer hC hx (by norm_num) hr hr'
    have hkx : act k x = x := hk.2
    have h := (hS.adj_act_iff hk.1.1 x (act r x)).2 hadj
    rw [hkx, act_act_eq_conj hkx, hkr] at h
    exact h
  have h1 := Set.ncard_le_ncard hsub (hS.finite.subset fun _ h => h.2.1)
  rw [Set.InjOn.ncard_image ((hS.act_injOn hC hx).mono (hS.labelLayer_subset hC 3)),
    hS.ncard_labelLayer_three hC, hS.valency x hx.1] at h1
  omega

theorem adj_iff_mem_labelLayer_two {x : V} (hx : x ∈ hexadFiber lab Y C ∅) {r : S}
    (hr : r ∈ ptStab act lab Y C) :
    (sliceGraph lab Y).Adj x (act r x) ↔ r ∈ labelLayer lab C 2 := by
  have ht := hS.lab_mul_self hx.1
  have hlabr : lab (act r x) = r * lab x * r⁻¹ := hS.lab_act r x
  have hrY : act r x ∈ Y := hS.mapsTo r hr.1 x hx.1
  obtain ⟨i, hi, hri⟩ := hS.exists_mem_labelLayer hC hr
  have hnot : ∀ {j : ℕ}, j ≠ 2 → r ∈ labelLayer lab C j → r ∉ labelLayer lab C 2 :=
    fun hj hrj hr2 => hj (eq_of_mem_labelLayer hrj hr2)
  interval_cases i
  · have hr2 := hnot (j := 0) (by decide) hri
    rw [labelLayer_zero, Set.mem_singleton_iff] at hri
    subst hri
    refine iff_of_false (fun h => ?_) hr2
    rw [map_one, Equiv.Perm.one_apply] at h
    exact (sliceGraph lab Y).loopless.irrefl x h
  · refine iff_of_false (fun h => ?_) (hnot (j := 1) (by decide) hri)
    rw [hS.labelLayer_one hC] at hri
    obtain ⟨a, ha, rfl⟩ := hri
    have hc := h.2.2.2
    rw [hlabr] at hc
    exact not_commute_conj_of_orderOf ht (hS.lab_mul_self (hC.1.1 ha))
      (hS.orderOf_lab_mul_of_mem_omega hC hx ha) hc
  · refine iff_of_true ⟨hx.1, hrY, fun h => ?_, ?_⟩ hri
    · have h1 := hS.eq_one_of_act_eq hC hx hr h.symm
      rw [h1] at hri
      have := eq_of_mem_labelLayer hri (by rw [labelLayer_zero]; rfl : (1 : S) ∈ labelLayer lab C 0)
      omega
    · rw [hlabr]
      rw [hS.labelLayer_two hC] at hri
      obtain ⟨a, ha, b, hb, hab, rfl⟩ := hri
      have hcab : Commute (lab a) (lab b) := (hC.1.2 ha hb hab).2.2.2
      exact commute_conj_mul_of_pow_three ht (hS.lab_mul_self (hC.1.1 ha))
        (hS.lab_mul_self (hC.1.1 hb)) hcab (hS.pow_three_lab_mul_of_mem_omega hC hx ha)
        (hS.pow_three_lab_mul_of_mem_omega hC hx hb)
  · exact iff_of_false (hS.not_adj_of_mem_labelLayer_three hC hx hri)
      (hnot (j := 3) (by decide) hri)

theorem inv_eq_self_of_mem {r : S} (hr : r ∈ ptStab act lab Y C) : r⁻¹ = r := by
  rw [hS.ptStab_eq_closure_of_isSliceMaxClique hC] at hr
  have h := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) r hr
  exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h)

theorem adj_act_act_iff {x : V} (hx : x ∈ hexadFiber lab Y C ∅) {r s : S}
    (hr : r ∈ ptStab act lab Y C) (hs : s ∈ ptStab act lab Y C) :
    (sliceGraph lab Y).Adj (act r x) (act s x) ↔ r * s ∈ labelLayer lab C 2 := by
  have h := hS.adj_act_iff ((sliceGroup lab Y).inv_mem hr.1) (act r x) (act s x)
  have e : act r⁻¹ (act s x) = act (r⁻¹ * s) x := by rw [map_mul, Equiv.Perm.mul_apply]
  rw [act_inv_act, e] at h
  rw [← h, hS.adj_iff_mem_labelLayer_two hC hx
    ((ptStab act lab Y C).mul_mem ((ptStab act lab Y C).inv_mem hr) hs),
    hS.inv_eq_self_of_mem hC hr]

omit hC [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] in
theorem commute_lab_of_act_eq {x : V} {k : S} (hk : act k x = x) : Commute (lab x) k := by
  have h := hS.lab_act k x
  rw [hk] at h
  change lab x * k = k * lab x
  conv_lhs => rw [h]
  group

omit [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] in
theorem act_lab_eq_act_lab {x : V} (hx : x ∈ hexadFiber lab Y C ∅) {a : V} (ha : a ∈ C) :
    act (lab x) a = act (lab a) x := by
  have haY := hC.1.1 ha
  refine hS.injOn (hS.mapsTo _ (lab_mem_sliceGroup hx.1) a haY)
    (hS.mapsTo _ (lab_mem_sliceGroup haY) x hx.1) ?_
  rw [hS.lab_act, hS.lab_act, inv_eq_of_mul_eq_one_right (hS.lab_mul_self hx.1),
    inv_eq_of_mul_eq_one_right (hS.lab_mul_self haY)]
  exact (braid_of_pow_three_eq_one (hS.lab_mul_self hx.1) (hS.lab_mul_self haY)
    (hS.pow_three_lab_mul_of_mem_omega hC hx ha)).symm

omit [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] in
theorem act_lab_act_lab {x : V} (hx : x ∈ hexadFiber lab Y C ∅) {a : V} (ha : a ∈ C) :
    act (lab x) (act (lab a) x) = a := by
  rw [← hS.act_lab_eq_act_lab hC hx ha, ← Equiv.Perm.mul_apply, ← map_mul,
    hS.lab_mul_self hx.1, map_one, Equiv.Perm.one_apply]

theorem act_lab_eq_of_mem_labelLayer_two {x : V} (hx : x ∈ hexadFiber lab Y C ∅) {r : S}
    (hr : r ∈ labelLayer lab C 2) : act (lab x) (act r x) = act r x := by
  have hadj := (hS.adj_iff_mem_labelLayer_two hC hx (hS.labelLayer_subset hC 2 hr)).2 hr
  exact (hS.act_lab_eq_iff hx.1 hadj.2.1).2 hadj.2.2.2

theorem act_lab_ne_of_mem_labelLayer_three {x : V} (hx : x ∈ hexadFiber lab Y C ∅) {r : S}
    (hr : r ∈ labelLayer lab C 3) : act (lab x) (act r x) ≠ act r x := by
  intro h
  have hrR := hS.labelLayer_subset hC 3 hr
  have hrY : act r x ∈ Y := hS.mapsTo r hrR.1 x hx.1
  have hc := (hS.act_lab_eq_iff hx.1 hrY).1 h
  have hne : x ≠ act r x := by
    intro e
    have h1 := hS.eq_one_of_act_eq hC hx hrR e.symm
    rw [h1] at hr
    have := eq_of_mem_labelLayer hr (by rw [labelLayer_zero]; rfl : (1 : S) ∈ labelLayer lab C 0)
    omega
  exact hS.not_adj_of_mem_labelLayer_three hC hx hr ⟨hx.1, hrY, hne, hc⟩

end Max

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
