module

public import CFSG.Timmesfeld.Bridge.Asc72XQuot

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp
open scoped commutatorElement

namespace CentralQuot

theorem zStar_eq_center_of_pCore_eq_bot {Y : Type} [Group Y] (h : CFSG.pCore 2 Y = ⊥) :
    zStar Y = Subgroup.center Y := by
  ext g
  rw [mem_zStar_iff, h, Subgroup.mem_center_iff]
  constructor
  · intro H y
    have hc := H y
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at hc
    exact hc.eq.symm
  · intro H y
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
    exact (H y).symm

theorem eq_one_of_mem_center {Y : Type} [Group Y] (h : CFSG.pCore 2 Y = ⊥) {c : Y}
    (hc : c ∈ Subgroup.center Y) (hcc : c * c = 1) : c = 1 := by
  have : (Subgroup.zpowers c).Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hc)
  have h1 := mem_pCore (z := c) hcc
  rw [h] at h1
  exact Subgroup.mem_bot.mp h1

variable {X : Type} [Group X] {z : X} [(Subgroup.zpowers z).Normal]

theorem pCore_quot_eq_bot (hzz : z * z = 1) (hO2 : CFSG.pCore 2 X ≤ Subgroup.zpowers z) :
    CFSG.pCore 2 (X ⧸ Subgroup.zpowers z) = ⊥ := by
  rw [← map_pCore hzz, eq_bot_iff]
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff x).mpr (hO2 hx)

section Cases

variable [Finite X]
  (hzc : z ∈ Subgroup.center X) (hzz : z * z = 1) {E : Set X} (hS : Setup X E) (hzE : z ∉ E)
  (hdisc : Disconnected E) {a b : X} (ha : a ∈ E) (hb : b ∈ E) (hab : a ≠ b) (hc : Commute a b)
  (habz : a * b * z ∈ E) (hO2 : CFSG.pCore 2 X ≤ Subgroup.zpowers z)
include hzc hzz hS hzE hdisc ha hb hab hc habz hO2

theorem involution_cases {t : X} (htt : t * t ∈ Subgroup.zpowers z) :
    t ∈ Subgroup.zpowers z ∨ t ∈ E ∨ t * z ∈ E := by
  by_cases htz : t ∈ Subgroup.zpowers z
  · exact Or.inl htz
  right
  obtain ⟨-, hB'⟩ := quot_facts hzc hzz hS hzE hdisc ha hb hab hc habz
  have hO2' := pCore_quot_eq_bot hzz hO2
  have hZ := zStar_eq_center_of_pCore_eq_bot hO2'
  set Xb := X ⧸ Subgroup.zpowers z with hXb
  have hB : CFSG.BenderSuzuki.IsBenderGroup (Xb ⧸ Subgroup.center Xb) :=
    isBenderGroup_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZ.symm) hB'
  set φ := QuotientGroup.mk' (Subgroup.center Xb) with hφdef
  have hinv : ∀ x : X, x ∉ Subgroup.zpowers z → x * x ∈ Subgroup.zpowers z →
      orderOf (φ (mk z x)) = 2 := by
    intro x hx hxx
    have hxx' : mk z x * mk z x = 1 := by
      rw [← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr hxx
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← map_mul, hxx', map_one]
    · intro h1
      have hc' : mk z x ∈ Subgroup.center Xb := (QuotientGroup.eq_one_iff _).mp h1
      have h2 := eq_one_of_mem_center hO2' hc' hxx'
      exact hx ((QuotientGroup.eq_one_iff x).mp h2)
  have haz : a ∉ Subgroup.zpowers z := by
    intro h
    rcases (mem_zpowers_of_mul_self hzz).mp h with h1 | h1
    · exact hS.oddT.ne_one ha h1
    · exact hzE (h1 ▸ ha)
  obtain ⟨c, hcj⟩ := isConj_iff.mp (IsBenderGroup.isConj_of_orderOf_eq_two hB
    (hinv t htz htt) (hinv a haz (by rw [hS.oddT.mul_self_eq_one ha]; exact Subgroup.one_mem _)))
  obtain ⟨hb', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Xb) c
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.zpowers z) hb'
  have hm : (mk z (h * t * h⁻¹))⁻¹ * mk z a ∈ Subgroup.center Xb := by
    have h1 : φ (mk z (h * t * h⁻¹)) = φ (mk z a) := by simpa only [map_mul, map_inv] using hcj
    simp only [hφdef, QuotientGroup.mk'_apply] at h1
    show ((h * t * h⁻¹ : X) : Xb)⁻¹ * (a : Xb) ∈ Subgroup.center Xb
    exact QuotientGroup.eq.mp h1
  set y := mk z (h * t * h⁻¹) with hydef
  set m := y⁻¹ * mk z a with hmdef
  have hyy : y * y = 1 := by
    rw [hydef, ← map_mul, show h * t * h⁻¹ * (h * t * h⁻¹) = h * (t * t) * h⁻¹ by group]
    exact (QuotientGroup.eq_one_iff _).mpr (‹(Subgroup.zpowers z).Normal›.conj_mem _ htt h)
  have haa : mk z a * mk z a = 1 := by rw [← map_mul, hS.oddT.mul_self_eq_one ha, map_one]
  have hmm : m * m = 1 := by
    have hcm := Subgroup.mem_center_iff.mp hm
    have e1 : mk z a = y * m := by rw [hmdef, mul_inv_cancel_left]
    have e2 : mk z a * mk z a = y * y * (m * m) := by
      rw [e1]
      calc y * m * (y * m) = y * (m * y) * m := by group
        _ = y * (y * m) * m := by rw [← hcm y]
        _ = y * y * (m * m) := by group
    rw [haa, hyy, one_mul] at e2
    exact e2.symm
  have hm1 : m = 1 := eq_one_of_mem_center hO2' hm hmm
  have hq : (h * t * h⁻¹)⁻¹ * a ∈ Subgroup.zpowers z := by
    rw [hmdef, inv_mul_eq_one, hydef] at hm1
    exact QuotientGroup.eq.mp (show ((h * t * h⁻¹ : X) : Xb) = (a : Xb) from hm1)
  have hzh : Commute h z := Subgroup.mem_center_iff.mp hzc h
  rcases (mem_zpowers_of_mul_self hzz).mp hq with h1 | h1
  ·
    left
    have h2 : h * t * h⁻¹ = a := inv_mul_eq_one.mp h1
    have h3 : t = h⁻¹ * a * h⁻¹⁻¹ := by rw [← h2]; group
    rw [h3]
    exact hS.conj_mem h⁻¹ ha
  ·
    right
    have h2 : a = h * t * h⁻¹ * z := by rw [← h1, mul_inv_cancel_left]
    have h3 : t * z = h⁻¹ * a * h⁻¹⁻¹ := by
      rw [h2, inv_inv]
      calc t * z = h⁻¹ * (h * t * h⁻¹) * (h * z * h⁻¹) * h := by group
        _ = h⁻¹ * (h * t * h⁻¹) * z * h := by rw [hzh.eq, mul_inv_cancel_right]
        _ = h⁻¹ * (h * t * h⁻¹ * z) * h := by group
    rw [h3]
    exact hS.conj_mem h⁻¹ ha

end Cases

end CentralQuot

end CFSG.Timmesfeld.Bridge.Asc72
