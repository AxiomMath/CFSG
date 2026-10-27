module

public import CFSG.Timmesfeld.CorollaryBBasic

public section

namespace CFSG.Timmesfeld.CorB

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X] {t : X}

theorem mem_center_of_forall_commute {G : Type*} [Group G] {S : Set G} (hS : closure S = ⊤)
    {u : G} (hu : ∀ s ∈ S, Commute u s) : u ∈ center G := by
  rw [mem_center_iff]
  intro g
  have hg : g ∈ closure S := hS ▸ mem_top g
  induction hg using closure_induction with
  | mem s hs => exact (hu s hs).symm.eq
  | one => rw [one_mul, mul_one]
  | mul x y _ _ hx hy => exact ((Commute.mul_left (a := x) (b := y) (c := u) hx hy))
  | inv x _ hx => exact (Commute.inv_left (a := x) (b := u) hx).eq

namespace Setup

variable (h : Setup t)
include h

theorem pow_four_eq_one_of_forall [Finite X]
    (hno : ∀ d ∈ cls t, ∀ e ∈ cls t, ¬ Commute d e → ¬ Odd (orderOf (d * e))) {d e : X}
    (hd : d ∈ cls t) (he : e ∈ cls t) : (d * e) ^ 4 = 1 := by
  rcases h.isRootInvolutionSet.2.1 d hd e he with h2 | h4 | hodd
  · rw [show 4 = 2 * 2 by norm_num, pow_mul, ← h2, pow_orderOf_eq_one, one_pow]
  · rw [← h4, pow_orderOf_eq_one]
  · have hc : Commute d e := by
      by_contra hc
      exact hno d hd e he hc hodd
    have h2 := (commute_iff_mul_sq_eq_one (h.mul_self hd) (h.mul_self he)).mp hc
    rw [show 4 = 2 * 2 by norm_num, pow_mul, h2, one_pow]

theorem isPGroup_normalClosure [Finite X]
    (hno : ∀ d ∈ cls t, ∀ e ∈ cls t, ¬ Commute d e → ¬ Odd (orderOf (d * e))) :
    IsPGroup 2 (normalClosure ({t} : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht : t ∈ CFSG.pCore 2 X := by
    rw [CFSG.BaerSuzuki.baer_suzuki_iff]
    intro g
    have hg := conj_mem_cls g (mem_cls_self t)
    refine isPGroup_two_closure_pair (k := 2) (h.mul_self (mem_cls_self t)) (h.mul_self hg) ?_
    rw [show 2 ^ 2 = 4 by norm_num]
    exact h.pow_four_eq_one_of_forall hno (mem_cls_self t) hg
  have := CFSG.BaerSuzuki.Helpers.pCore_normal (G := X) 2
  have hle : normalClosure ({t} : Set X) ≤ CFSG.pCore 2 X :=
    normalClosure_le_normal (Set.singleton_subset_iff.mpr ht)
  exact (CFSG.BaerSuzuki.Helpers.pCore_isPGroup 2).to_le hle

theorem exists_opposite [Finite X] (h4 : ∃ d ∈ cls t, ∃ e ∈ cls t, orderOf (d * e) = 4) :
    ∃ d ∈ cls t, ∃ e ∈ cls t, ¬ Commute d e ∧ Odd (orderOf (d * e)) := by
  by_contra hno'
  have hno : ∀ d ∈ cls t, ∀ e ∈ cls t, ¬ Commute d e → ¬ Odd (orderOf (d * e)) :=
    fun d hd e he hc ho => hno' ⟨d, hd, e, he, hc, ho⟩
  set U := normalClosure ({t} : Set X)
  have hP : IsPGroup 2 ↥U := h.isPGroup_normalClosure hno
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥U := hP.isNilpotent
  obtain ⟨n, hn⟩ := Group.IsNilpotent.nilpotent ↥U
  classical
  have hex : ∃ j, ∃ u ∈ clsIn t, u ∈ Subgroup.upperCentralSeries ↥U j :=
    ⟨n, ⟨t, cls_subset t (mem_cls_self t)⟩, mem_cls_self t, by rw [hn]; exact mem_top _⟩
  obtain ⟨u, hu, huj⟩ := Nat.find_spec hex
  have hmin : ∀ i < Nat.find hex, ∀ v ∈ clsIn t, v ∉ Subgroup.upperCentralSeries ↥U i :=
    fun i hi v hv hvi => Nat.find_min hex hi ⟨v, hv, hvi⟩
  have hu2 := h.mul_self hu
  have hsq : ∀ v ∈ clsIn t, ⁅u, v⁆ = (u * v) ^ 2 := by
    intro v hv
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right (Subtype.ext hu2)
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (Subtype.ext (h.mul_self hv))
    rw [commutatorElement_def, hui, hvi, pow_two, mul_assoc]
  obtain ⟨d, hd, e, he, hde⟩ := h4
  have hnc : ¬ Commute d e := by
    intro hc
    have h2 := (commute_iff_mul_sq_eq_one (h.mul_self hd) (h.mul_self he)).mp hc
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hde] at this
    exact absurd this (by norm_num)
  rcases hj : Nat.find hex with _ | _ | i
  · rw [hj, Subgroup.upperCentralSeries_zero, mem_bot] at huj
    have h2 := h.orderOf_mem hu
    rw [huj] at h2
    simp at h2
  · rw [hj, Subgroup.upperCentralSeries_one] at huj
    exact hnc (forall_commute_of_mem_center huj hu d hd e he)
  · rw [hj] at huj hmin
    have hcomm : ∀ v ∈ clsIn t, Commute u v := by
      intro v hv
      have hc := Subgroup.mem_upperCentralSeries_succ_iff.mp huj v
      rw [hsq v hv] at hc
      by_contra hnuv
      have hne : (u * v) ^ 2 ≠ 1 := fun h1 => hnuv
        ((commute_iff_mul_sq_eq_one (Subtype.ext hu2) (Subtype.ext (h.mul_self hv))).mpr h1)
      have h4' : ((u : X) * (v : X)) ^ 4 = 1 := h.pow_four_eq_one_of_forall hno hu hv
      have hord : orderOf ((u : X) * (v : X)) = 4 := by
        have hdvd := orderOf_dvd_of_pow_eq_one h4'
        have hle : orderOf ((u : X) * (v : X)) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
        have hne' : ((u : X) * (v : X)) ^ 2 ≠ 1 := fun h1 => hne (Subtype.ext (by simpa using h1))
        interval_cases hk : orderOf ((u : X) * (v : X))
        · exact absurd (orderOf_eq_zero_iff'.mp hk 4 (by norm_num)) (by simpa using h4')
        · exact absurd (by rw [orderOf_eq_one_iff.mp hk, one_pow]) hne'
        · exact absurd (by rw [← hk, pow_orderOf_eq_one]) hne'
        · exact absurd hdvd (by norm_num)
        · rfl
      have hmem : (u * v) ^ 2 ∈ clsIn t := by
        rw [mem_clsIn]
        push_cast
        exact h.isRootInvolutionSet.2.2 _ hu _ hv hord
      exact hmin (i + 1) (by omega) _ hmem hc
    have hc := mem_center_of_forall_commute (closure_clsIn t) hcomm
    rw [← Subgroup.upperCentralSeries_one] at hc
    exact hmin (i + 1) (by omega) u hu (Subgroup.upperCentralSeries_mono ↥U (by omega) hc)

end Setup

end CFSG.Timmesfeld.CorB
