module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open Subgroup

theorem exists_lift_inverted_of_center_three {L : Type} [Group L] [Finite L] {z : L}
    (hz : z ∈ center L) (hz3 : orderOf z = 3) (hZ : Nat.card (center L) = 3) {σ : MulAut L}
    (hσz : σ z = z) {σ' : MulAut (L ⧸ center L)}
    (hσ' : ∀ l : L, σ' (l : L ⧸ center L) = ((σ l : L) : L ⧸ center L))
    {x : L ⧸ center L} (hx : orderOf x = 3) (hinv : σ' x = x⁻¹) :
    ∃ a : L, (a : L ⧸ center L) = x ∧ σ a = a⁻¹ ∧ orderOf a = 3 := by
  have hcardz : Nat.card (Subgroup.zpowers z) = 3 := by
    classical
    haveI : Fintype L := Fintype.ofFinite L
    rw [Nat.card_eq_fintype_card, Fintype.card_zpowers, hz3]
  have hcenter : center L = Subgroup.zpowers z := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_).symm
    simp [hZ, hcardz]
  obtain ⟨x0, hx0⟩ := QuotientGroup.mk_surjective x
  have hq : ((σ x0 : L) : L ⧸ center L) = ((x0⁻¹ : L) : L ⧸ center L) := by
    rw [← hσ' x0, hx0, hinv, QuotientGroup.mk_inv, hx0]
  set w : L := (σ x0) / x0⁻¹ with hwdef
  have hwmem : w ∈ center L := by
    rw [hwdef]
    exact QuotientGroup.eq_iff_div_mem.mp hq
  have hwz : w ∈ Subgroup.zpowers z := by
    rw [← hcenter]
    exact hwmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwz
  have hσw : σ w = w := by
    rw [← hk, map_zpow σ z k, hσz]
  have hw3 : w ^ 3 = 1 := by
    have hdvd : orderOf w ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers z) hwz
      rwa [hcardz] at h
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hww : w * w = w⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_two, ← pow_succ]
    exact hw3
  have hσx0 : σ x0 = x0⁻¹ * w := by
    have h2 : σ x0 = w * x0⁻¹ := by
      rw [hwdef, div_eq_mul_inv, inv_inv, mul_assoc, mul_inv_cancel, mul_one]
    rw [h2]
    exact (Subgroup.mem_center_iff.mp hwmem x0⁻¹).symm
  set a : L := x0 * w with hadef
  have hwq : ((w : L) : L ⧸ center L) = 1 := (QuotientGroup.eq_one_iff w).mpr hwmem
  have haq : ((a : L) : L ⧸ center L) = x := by
    rw [hadef, QuotientGroup.mk_mul, hwq, mul_one, hx0]
  have hσa : σ a = a⁻¹ := by
    rw [hadef, map_mul σ x0 w, hσx0, hσw, mul_inv_rev, mul_assoc, hww,
      (Subgroup.mem_center_iff.mp (inv_mem hwmem) x0⁻¹).symm]
  have hx3 : x ^ 3 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have ha3mem : a ^ 3 ∈ center L := by
    rw [← QuotientGroup.eq_one_iff (a ^ 3)]
    rw [QuotientGroup.mk_pow, haq, hx3]
  have hza : a ^ 3 ∈ Subgroup.zpowers z := by
    rw [← hcenter]
    exact ha3mem
  have hσfix : σ (a ^ 3) = a ^ 3 := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hza
    rw [← hm, map_zpow σ z m, hσz]
  have hσa3 : σ (a ^ 3) = (a ^ 3)⁻¹ := by
    rw [map_pow σ a 3, hσa, inv_pow]
  have hb2 : (a ^ 3) ^ 2 = 1 := by
    rw [pow_two]
    exact eq_inv_iff_mul_eq_one.mp (hσfix.symm.trans hσa3)
  have hb3 : (a ^ 3) ^ 3 = 1 := by
    have hdvd : orderOf (a ^ 3) ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers z) hza
      rwa [hcardz] at h
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have ha3 : a ^ 3 = 1 := by
    have h : (a ^ 3) ^ 3 = (a ^ 3) * (a ^ 3) ^ 2 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ']
    rw [h, hb2, mul_one] at hb3
    exact hb3
  have hxne : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    exact absurd hx (by decide)
  have hane : a ≠ 1 := by
    intro ha1
    apply hxne
    calc x = (a : L ⧸ center L) := haq.symm
      _ = ((1 : L) : L ⧸ center L) := by rw [ha1]
      _ = 1 := QuotientGroup.mk_one (center L)
  exact ⟨a, haq, hσa, orderOf_eq_prime ha3 hane⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
