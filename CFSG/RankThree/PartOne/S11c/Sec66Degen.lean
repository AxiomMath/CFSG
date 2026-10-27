module

public import CFSG.RankThree.PartOne.S11c.Sec66TFamily

public section

namespace CFSG.RankThree.PartOne.Sec66T

open Subgroup

theorem center_eq_bot_of_mulEquiv {T G : Type*} [Group T] [Group G] (e : T ≃* G)
    (h : Subgroup.center G = ⊥) : Subgroup.center T = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxG : e x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_center_iff.mp hx (e.symm g)
    simpa using congrArg e this
  rw [h, Subgroup.mem_bot] at hxG
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [hxG, map_one])

theorem card_fixSub_eq_of_conj {T C : Type} [Group T] [Group C] (e : T ≃* C) (α : MulAut T)
    (β ψ : MulAut C) (hψ : fixSub (ψ * MulAut.congr e α * ψ⁻¹) = fixSub β) :
    Nat.card (fixSub α) = Nat.card (fixSub β) := by
  have e12 : ↥(fixSub α) ≃* ↥(fixSub β) :=
    ((fixSubEquiv e α).trans (fixSubEquiv ψ (MulAut.congr e α))).trans
      (MulEquiv.subgroupCongr hψ)
  exact Nat.card_congr e12.toEquiv

theorem exists_noncomm_of_perfect {G : Type*} [Group G] [Nontrivial G]
    (hperf : commutator G = ⊤) : ∃ x y : G, x * y ≠ y * x := by
  by_contra h
  push Not at h
  have hc : Subgroup.center G = ⊤ :=
    eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun g => h g x
  have hb : commutator G = ⊥ := (commutator_eq_bot_iff_center_eq_top _).mpr hc
  rw [hb] at hperf
  exact bot_ne_top hperf

theorem eq_bot_of_isPGroup_two_of_odd {G : Type*} [Group G] [Finite G] {R C : Subgroup G}
    (hR : IsPGroup 2 ↥R) (hle : R ≤ C) (hodd : Odd (Nat.card C)) : R = ⊥ := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hR
  have hdvd : Nat.card R ∣ Nat.card C := Subgroup.card_dvd_of_le hle
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hne
    have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 hne
    have h3 : 2 ∣ Nat.card C := h2.trans hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h3)
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq R hk

theorem false_of_two_group_in_card_twenty {G : Type*} [Group G] [Finite G] {R C : Subgroup G}
    (hR : IsPGroup 2 ↥R) (hle : R ≤ C) (hC : Nat.card C = 20) (h16 : 16 ≤ Nat.card R) :
    False := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hR
  have hdvd : Nat.card R ∣ Nat.card C := Subgroup.card_dvd_of_le hle
  rw [hk, hC] at hdvd
  rw [hk] at h16
  have hk4 : 4 ≤ k := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h4 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 hk4
  have : 2 ^ 4 ∣ 20 := h4.trans hdvd
  omega

end CFSG.RankThree.PartOne.Sec66T
