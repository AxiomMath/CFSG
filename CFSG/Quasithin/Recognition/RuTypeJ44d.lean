module

public import CFSG.Quasithin.Recognition.RuTypeJ44c

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped MatrixGroups

namespace SL3

theorem R2m_inf_R0 : ∀ g ∈ R2m, g ∈ R0 → g = 1 ∨ g = zP0 := by decide +kernel

end SL3

namespace RuDataM

variable {G : Type} [Group G] (M : RuDataM G) [Finite G]

section Five

variable {M} {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
include hbH hb5

theorem prod_actQ_eq_one {c : G} (hcH : c ∈ ruH M.T)
    (hc5 : orderOf c = 5) (hcb : c * b * c⁻¹ = b) {x : M.Qbar} (hx : x ∈ M.Q5bar ⟨b, hbH⟩) :
    (M.actQ ⟨c, hcH⟩)^[1] x * (M.actQ ⟨c, hcH⟩)^[2] x * (M.actQ ⟨c, hcH⟩)^[3] x *
      (M.actQ ⟨c, hcH⟩)^[4] x * (M.actQ ⟨c, hcH⟩)^[5] x = 1 := by
  let _ : CommGroup M.Qbar := M.qbarComm
  have hcq : c * b * c⁻¹ = b ^ 1 * 1 := by rw [hcb, pow_one, mul_one]
  have hmem : ∀ i : ℕ, (M.actQ ⟨c, hcH⟩)^[i] x ∈ M.Q5bar ⟨b, hbH⟩ := by
    intro i
    induction i with
    | zero => exact hx
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact M.Q5bar_conj hbH hcH (one_mem _) hcq ih
  set s := (M.actQ ⟨c, hcH⟩)^[1] x * (M.actQ ⟨c, hcH⟩)^[2] x * (M.actQ ⟨c, hcH⟩)^[3] x *
    (M.actQ ⟨c, hcH⟩)^[4] x * (M.actQ ⟨c, hcH⟩)^[5] x with hs
  have h6 : (M.actQ ⟨c, hcH⟩)^[6] x = (M.actQ ⟨c, hcH⟩)^[1] x := by
    rw [show 6 = 1 + 5 from rfl, Function.iterate_add_apply, actQ_b_iterate_five hcH hc5]
  have e1 : M.actQ ⟨c, hcH⟩ ((M.actQ ⟨c, hcH⟩)^[1] x) = (M.actQ ⟨c, hcH⟩)^[2] x :=
    (Function.iterate_succ_apply' _ 1 x).symm
  have e2 : M.actQ ⟨c, hcH⟩ ((M.actQ ⟨c, hcH⟩)^[2] x) = (M.actQ ⟨c, hcH⟩)^[3] x :=
    (Function.iterate_succ_apply' _ 2 x).symm
  have e3 : M.actQ ⟨c, hcH⟩ ((M.actQ ⟨c, hcH⟩)^[3] x) = (M.actQ ⟨c, hcH⟩)^[4] x :=
    (Function.iterate_succ_apply' _ 3 x).symm
  have e4 : M.actQ ⟨c, hcH⟩ ((M.actQ ⟨c, hcH⟩)^[4] x) = (M.actQ ⟨c, hcH⟩)^[5] x :=
    (Function.iterate_succ_apply' _ 4 x).symm
  have e5 : M.actQ ⟨c, hcH⟩ ((M.actQ ⟨c, hcH⟩)^[5] x) = (M.actQ ⟨c, hcH⟩)^[6] x :=
    (Function.iterate_succ_apply' _ 5 x).symm
  have hfix : M.actQ ⟨c, hcH⟩ s = s := by
    rw [hs, map_mul, map_mul, map_mul, map_mul, e1, e2, e3, e4, e5, h6,
      mul_comm _ ((M.actQ ⟨c, hcH⟩)^[1] x)]
    simp only [mul_assoc]
  have hsQ5 : s ∈ M.Q5bar ⟨b, hbH⟩ :=
    mul_mem (mul_mem (mul_mem (mul_mem (hmem 1) (hmem 2)) (hmem 3)) (hmem 4)) (hmem 5)
  have hsC : s ∈ M.HCbar := by
    rw [← ker_dQ hcH hc5, MonoidHom.mem_ker, M.dQ_apply, mul_inv_eq_one]
    exact hfix
  have hbot : s ∈ M.Q5bar ⟨b, hbH⟩ ⊓ M.HCbar := Subgroup.mem_inf.mpr ⟨hsQ5, hsC⟩
  rw [Q5bar_inf_HCbar hbH hb5, Subgroup.mem_bot] at hbot
  exact hbot

theorem mem_Q5_of_pow_five {k : ℕ} {q : G} (hq : q ∈ ruQ M.T)
    (h5 : (b ^ k * q) ^ 5 = 1) : q ∈ M.Q5 hbH := by
  by_cases hk : 5 ∣ k
  · obtain ⟨j, rfl⟩ := hk
    have hbk : b ^ (5 * j) = 1 := by rw [pow_mul, pow_five_of_orderOf hb5, one_pow]
    rw [hbk, one_mul] at h5
    have h1 : orderOf q ∣ 5 := orderOf_dvd_of_pow_eq_one h5
    have h2 : orderOf q ∣ 2 ^ 11 := by
      rw [← M.toRuData.card_Q]
      exact Subgroup.orderOf_dvd_natCard _ hq
    rcases (Nat.dvd_prime Nat.prime_five).mp h1 with h | h
    · rw [orderOf_eq_one_iff.mp h]
      exact one_mem _
    · rw [h] at h2
      norm_num at h2
  · have hbkH : b ^ k ∈ ruH M.T := pow_mem hbH k
    have hcop : Nat.Coprime 5 k := (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hk
    have hbk5 : orderOf (b ^ k) = 5 := by
      rw [orderOf_pow, hb5, Nat.Coprime.gcd_eq_one hcop, Nat.div_one]
    obtain ⟨a, ha, c, hc, hac⟩ := exists_Q5_mul_HC hbH hb5 hq
    obtain ⟨haQ, haQ5⟩ := (M.mem_Q5 hbH).mp ha
    have hcQ : c ∈ ruQ M.T := M.HC_le_Q hc
    have hB5 : (b ^ k) ^ 5 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, pow_five_of_orderOf hb5, one_pow]
    have key : ∀ X : G, X ^ 1 * q * (X ^ 1)⁻¹ * (X ^ 2 * q * (X ^ 2)⁻¹) *
        (X ^ 3 * q * (X ^ 3)⁻¹) * (X ^ 4 * q * (X ^ 4)⁻¹) * (X ^ 5 * q * (X ^ 5)⁻¹) =
        (X * q) ^ 5 * (X ^ 5)⁻¹ := fun X => by
      simp only [pow_succ, pow_zero, one_mul]
      group
    have hprod : M.conjQ (⟨b ^ k, hbkH⟩ ^ 1) ⟨q, hq⟩ * M.conjQ (⟨b ^ k, hbkH⟩ ^ 2) ⟨q, hq⟩ *
        M.conjQ (⟨b ^ k, hbkH⟩ ^ 3) ⟨q, hq⟩ * M.conjQ (⟨b ^ k, hbkH⟩ ^ 4) ⟨q, hq⟩ *
        M.conjQ (⟨b ^ k, hbkH⟩ ^ 5) ⟨q, hq⟩ = 1 := by
      apply Subtype.ext
      show (b ^ k) ^ 1 * q * ((b ^ k) ^ 1)⁻¹ * ((b ^ k) ^ 2 * q * ((b ^ k) ^ 2)⁻¹) *
          ((b ^ k) ^ 3 * q * ((b ^ k) ^ 3)⁻¹) * ((b ^ k) ^ 4 * q * ((b ^ k) ^ 4)⁻¹) *
          ((b ^ k) ^ 5 * q * ((b ^ k) ^ 5)⁻¹) = 1
      rw [key, h5, hB5, inv_one, one_mul]
    have hit : ∀ i : ℕ, ((M.conjQ (⟨b ^ k, hbkH⟩ ^ i) ⟨q, hq⟩ : ruQ M.T) : M.Qbar) =
        (M.actQ ⟨b ^ k, hbkH⟩)^[i] ((⟨q, hq⟩ : ruQ M.T) : M.Qbar) := fun i => by
      rw [M.actQ_iterate, M.actQ_mk]
    have hmk := congrArg (fun x : ruQ M.T => (x : M.Qbar)) hprod
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_one, hit] at hmk
    have hqac : ((⟨q, hq⟩ : ruQ M.T) : M.Qbar) =
        ((⟨a, haQ⟩ : ruQ M.T) : M.Qbar) * ((⟨c, hcQ⟩ : ruQ M.T) : M.Qbar) := by
      rw [← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hac
    have hc1 : M.actQ ⟨b ^ k, hbkH⟩ ((⟨c, hcQ⟩ : ruQ M.T) : M.Qbar) =
        ((⟨c, hcQ⟩ : ruQ M.T) : M.Qbar) := by
      have hker : ((⟨c, hcQ⟩ : ruQ M.T) : M.Qbar) ∈ (M.dQ ⟨b ^ k, hbkH⟩).ker := by
        rw [ker_dQ hbkH hbk5]
        exact (M.mem_HCbar_mk _).mpr hc
      rw [MonoidHom.mem_ker, M.dQ_apply, mul_inv_eq_one] at hker
      exact hker
    have hcfix := Function.iterate_fixed hc1
    simp only [hqac, iterate_map_mul, hcfix] at hmk
    have hBb : b ^ k * b * (b ^ k)⁻¹ = b := by group
    have hnorm := prod_actQ_eq_one hbH hb5 hbkH hbk5 hBb haQ5
    have hre : ∀ y1 y2 y3 y4 y5 c : M.Qbar, y1 * c * (y2 * c) * (y3 * c) * (y4 * c) * (y5 * c) =
        (y1 * y2 * y3 * y4 * y5) * ((c * c) * (c * c) * c) := by
      intro y1 y2 y3 y4 y5 c
      rw [M.qbar_rearr y1 c y2 c, M.qbar_rearr (y1 * y2) (c * c) y3 c,
        M.qbar_rearr (y1 * y2 * y3) (c * c * c) y4 c,
        M.qbar_rearr (y1 * y2 * y3 * y4) (c * c * c * c) y5 c]
      simp only [mul_assoc]
    rw [hre, hnorm, one_mul] at hmk
    simp only [M.Qbar_sq, one_mul] at hmk
    have hcU : c ∈ ruU M.L M.T := by
      have := (QuotientGroup.eq_one_iff _).mp hmk
      rwa [Subgroup.mem_subgroupOf] at this
    rw [hac]
    exact mul_mem ha (M.U_le_Q5 hbH hcU)

end Five

theorem Agrp_conj_b5el_Q5 {y : G} (hy : y ∈ M.Agrp) :
    ∃ k : ℕ, ∃ q ∈ M.Q5 M.b5el_mem_H, y * M.b5el * y⁻¹ = M.b5el ^ k * q := by
  obtain ⟨k, q, hq, hk⟩ := M.Agrp_conj_b5el hy
  refine ⟨k, q, mem_Q5_of_pow_five M.b5el_mem_H M.orderOf_b5el (k := k) hq ?_, hk⟩
  rw [← hk]
  have e : (y * M.b5el * y⁻¹) ^ 5 = y * M.b5el ^ 5 * y⁻¹ := by
    simp only [conj_pow]
  rw [e, pow_five_of_orderOf M.orderOf_b5el, mul_one, mul_inv_cancel]

noncomputable abbrev B5Q5 : Subgroup G := M.Q5 M.b5el_mem_H ⊔ Subgroup.zpowers M.b5el

theorem zpowers_b5el_le_H : Subgroup.zpowers M.b5el ≤ ruH M.T :=
  (Subgroup.zpowers_le).mpr M.b5el_mem_H

theorem zpowers_le_normalizer_Q5 :
    Subgroup.zpowers M.b5el ≤ Subgroup.normalizer (M.Q5 M.b5el_mem_H : Set G) := by
  intro g hg
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hgb : M.b5el ^ i * M.b5el * (M.b5el ^ i)⁻¹ = M.b5el ^ 1 * 1 := by group
  exact M.conj_mem_Q5 M.b5el_mem_H (M.zpowers_b5el_le_H hg) (one_mem _) hgb hx

theorem mem_B5Q5 {x : G} (hx : x ∈ M.B5Q5) :
    ∃ q ∈ M.Q5 M.b5el_mem_H, ∃ i : ℤ, x = q * M.b5el ^ i := by
  have hx' : x ∈ ((M.Q5 M.b5el_mem_H ⊔ Subgroup.zpowers M.b5el : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ M.zpowers_le_normalizer_Q5] at hx'
  obtain ⟨q, hq, z, hz, rfl⟩ := hx'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact ⟨q, hq, i, rfl⟩

theorem B5Q5_le_H : M.B5Q5 ≤ ruH M.T := sup_le M.Q5_le_H M.zpowers_b5el_le_H

theorem Agrp_conj_B5Q5 {y x : G} (hy : y ∈ M.Agrp)
    (hx : x ∈ M.B5Q5) : y * x * y⁻¹ ∈ M.B5Q5 := by
  refine conj_mem_sup_of (fun q hq => Subgroup.mem_sup_left (M.Agrp_conj_Q5 hy hq))
    (fun z hz => ?_) hx
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  obtain ⟨k, q, hq, hk⟩ := M.Agrp_conj_b5el_Q5 hy
  rw [← conj_zpow, hk]
  exact zpow_mem (mul_mem (Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers _) k))
    (Subgroup.mem_sup_left hq)) i

theorem Agrp_le_normalizer_B5Q5 :
    M.Agrp ≤ Subgroup.normalizer (M.B5Q5 : Set G) :=
  fun _ hy => mem_normalizer_of_conj_mem fun _ hx => M.Agrp_conj_B5Q5 hy hx

theorem Agrp_le_normalizer_Q5 :
    M.Agrp ≤ Subgroup.normalizer (M.Q5 M.b5el_mem_H : Set G) :=
  fun _ hy => mem_normalizer_of_conj_mem fun _ hx => M.Agrp_conj_Q5 hy hx

noncomputable abbrev TF : Subgroup G :=
  M.Agrp ⊔ M.Q5 M.b5el_mem_H

noncomputable abbrev F1 : Subgroup G := M.Agrp ⊔ M.B5Q5

theorem TF_le_F1 : M.TF ≤ M.F1 :=
  sup_le_sup_left le_sup_left _

theorem TF_le_H : M.TF ≤ ruH M.T :=
  sup_le M.Agrp_le_H M.Q5_le_H

theorem F1_le_H : M.F1 ≤ ruH M.T :=
  sup_le M.Agrp_le_H M.B5Q5_le_H

theorem TF_le_T : M.TF ≤ (M.T : Subgroup G) :=
  sup_le M.Agrp_le_T M.Q5_le_T

theorem Agrp_inf_Q_le_Y : M.Agrp ⊓ ruQ M.T ≤ M.Ygrp := by
  rintro y ⟨hyA, hyQ⟩
  rw [← M.Q5W_inf_Q]
  refine Subgroup.mem_inf.mpr ⟨?_, hyQ⟩
  have hyL := M.Agrp_le_L hyA
  have hθR2 : M.θ ⟨y, hyL⟩ ∈ SL3.R2m := (mem_pullL.mp (M.Agrp_le_R2 hyA)).2
  have hθR0 : M.θ ⟨y, hyL⟩ ∈ SL3.R0 := by
    rw [← M.θQ_eq]
    exact ⟨⟨y, hyL⟩, Subgroup.mem_subgroupOf.mpr hyQ, rfl⟩
  rcases SL3.R2m_inf_R0 _ hθR2 hθR0 with h | h
  · have hyW : y ∈ M.W := by
      rw [← M.Agrp_inf_S]
      exact ⟨hyA, (M.mem_S_iff_θ hyL).mpr h⟩
    exact Subgroup.mem_sup_right hyW
  · have hL : M.ael⁻¹ * y ∈ M.L := mul_mem (inv_mem M.ael_mem_L) hyL
    have hW : M.ael⁻¹ * y ∈ M.W := by
      rw [← M.Agrp_inf_S]
      have hA : M.ael⁻¹ * y ∈ M.Agrp := mul_mem (inv_mem M.ael_mem_Agrp) hyA
      refine ⟨hA, (M.mem_S_iff_θ hL).mpr ?_⟩
      have e : (⟨M.ael⁻¹ * y, hL⟩ : M.L) = (⟨M.ael, M.ael_mem_L⟩ : M.L)⁻¹ * ⟨y, hyL⟩ := rfl
      rw [e, map_mul, map_inv, h, M.θ_ael, inv_mul_cancel]
    have e : y = M.ael * (M.ael⁻¹ * y) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left M.ael_mem_Q5) (Subgroup.mem_sup_right hW)

theorem mem_Q_of_mul_zpow_mem_Q {y : G} (hyH : y ∈ ruH M.T) {m : ℕ} (hy2 : y ^ 2 ^ m = 1)
    {i : ℤ} (hQ : y * M.b5el ^ i ∈ ruQ M.T) : y ∈ ruQ M.T ∧ M.b5el ^ i = 1 := by
  have hbi : M.b5el ^ i ∈ ruH M.T := zpow_mem M.b5el_mem_H i
  have hk : (⟨y * M.b5el ^ i, mul_mem hyH hbi⟩ : ruH M.T) ∈ M.σ5.ker := by
    rw [M.σ5_ker, Subgroup.mem_subgroupOf]
    exact hQ
  have hσ : M.σ5 ⟨y, hyH⟩ = (M.σ5 ⟨M.b5el ^ i, hbi⟩)⁻¹ := by
    have e : (⟨y * M.b5el ^ i, mul_mem hyH hbi⟩ : ruH M.T) = ⟨y, hyH⟩ * ⟨M.b5el ^ i, hbi⟩ := rfl
    rw [MonoidHom.mem_ker, e, map_mul] at hk
    exact eq_inv_of_mul_eq_one_left hk
  have hb5i : (M.b5el ^ i) ^ 5 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      pow_five_of_orderOf M.orderOf_b5el, one_zpow]
  have h5 : (M.σ5 ⟨y, hyH⟩) ^ 5 = 1 := by
    rw [hσ, inv_pow, ← map_pow]
    have : (⟨M.b5el ^ i, hbi⟩ : ruH M.T) ^ 5 = 1 := Subtype.ext hb5i
    rw [this, map_one, inv_one]
  have h2 : (M.σ5 ⟨y, hyH⟩) ^ 2 ^ m = 1 := by
    rw [← map_pow]
    have : (⟨y, hyH⟩ : ruH M.T) ^ 2 ^ m = 1 := Subtype.ext hy2
    rw [this, map_one]
  have h1 : M.σ5 ⟨y, hyH⟩ = 1 := by
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h5) (orderOf_dvd_of_pow_eq_one h2)
    have : Nat.gcd 5 (2 ^ m) = 1 := Nat.Coprime.pow_right m (by norm_num)
    rw [this, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  have hyQ : y ∈ ruQ M.T := by
    have : (⟨y, hyH⟩ : ruH M.T) ∈ M.σ5.ker := h1
    rw [M.σ5_ker, Subgroup.mem_subgroupOf] at this
    exact this
  refine ⟨hyQ, ?_⟩
  have hbiQ : M.b5el ^ i ∈ ruQ M.T := by
    have e : M.b5el ^ i = y⁻¹ * (y * M.b5el ^ i) := by group
    rw [e]
    exact mul_mem (inv_mem hyQ) hQ
  have hd1 : orderOf (M.b5el ^ i) ∣ 5 := orderOf_dvd_of_pow_eq_one hb5i
  have hd2 : orderOf (M.b5el ^ i) ∣ 2 ^ 11 := by
    rw [← M.toRuData.card_Q]
    exact Subgroup.orderOf_dvd_natCard _ hbiQ
  have hd := Nat.dvd_gcd hd1 hd2
  have : Nat.gcd 5 (2 ^ 11) = 1 := by norm_num
  rw [this, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

theorem pow_eq_one_of_mem_Agrp {y : G} (hy : y ∈ M.Agrp) :
    y ^ 2 ^ 11 = 1 := by
  have h := Subgroup.orderOf_dvd_natCard _ hy
  rw [M.card_Agrp] at h
  exact orderOf_dvd_iff_pow_eq_one.mp h

theorem F1_inf_Q : M.F1 ⊓ ruQ M.T = M.Ygrp := by
  refine le_antisymm ?_ (le_inf ?_ (M.Y_le_Q5W_inf_Q.trans inf_le_right))
  · rintro x ⟨hxF, hxQ⟩
    have hx' : x ∈ ((M.Agrp ⊔ M.B5Q5 : Subgroup G) : Set G) := hxF
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ M.Agrp_le_normalizer_B5Q5] at hx'
    obtain ⟨y, hy, z, hz, rfl⟩ := hx'
    obtain ⟨q, hq, i, rfl⟩ := M.mem_B5Q5 hz
    have hyH := M.Agrp_le_H hy
    have hqQ := M.Q5_le_Q _ hq
    have hyb : y * M.b5el ^ i ∈ ruQ M.T := by
      have e : y * M.b5el ^ i = (y * q * y⁻¹)⁻¹ * (y * (q * M.b5el ^ i)) := by group
      rw [e]
      exact mul_mem (inv_mem (M.conj_mem_Q hyH hqQ)) hxQ
    obtain ⟨hyQ, hbi⟩ := M.mem_Q_of_mul_zpow_mem_Q hyH (M.pow_eq_one_of_mem_Agrp hy) hyb
    rw [hbi, mul_one]
    exact mul_mem (M.Agrp_inf_Q_le_Y ⟨hy, hyQ⟩) (Subgroup.mem_sup_left hq)
  · exact sup_le ((le_sup_left : M.Q5 M.b5el_mem_H ≤ M.B5Q5).trans le_sup_right)
      (M.Q0_le_W.trans (M.W_le_Agrp.trans le_sup_left))

theorem TF_inf_Q : M.TF ⊓ ruQ M.T = M.Ygrp := by
  refine le_antisymm ?_ (le_inf ?_ (M.Y_le_Q5W_inf_Q.trans inf_le_right))
  · rw [← M.F1_inf_Q]
    exact inf_le_inf_right _ M.TF_le_F1
  · exact sup_le le_sup_right (M.Q0_le_W.trans (M.W_le_Agrp.trans le_sup_left))

theorem card_Agrp_inf_Q5 :
    Nat.card ↥(M.Agrp ⊓ M.Q5 M.b5el_mem_H) = 2 ^ 8 := by
  have hle : M.Agrp ⊓ M.Q5 M.b5el_mem_H ≤ M.L := inf_le_left.trans M.Agrp_le_L
  set f : ↥(M.Agrp ⊓ M.Q5 M.b5el_mem_H) →* SL(3, ZMod 2) := M.θ.comp (Subgroup.inclusion hle)
  have h := Subgroup.card_ker_mul_card_range f
  have hS : ∀ (x : G) (hx : x ∈ M.L), M.θ ⟨x, hx⟩ = 1 ↔ x ∈ ruS M.L := fun x hx =>
    (M.mem_S_iff_θ hx).symm
  have hker : Nat.card f.ker = 2 ^ 7 := by
    rw [← M.card_Q5_inf_S M.b5el_mem_H M.orderOf_b5el]
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2.2, (hS _ _).mp x.2⟩
        invFun := fun y => ⟨⟨y.1, ?_, y.2.1⟩, (hS _ _).mpr y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hyW : (y : G) ∈ M.W := M.Q5_inf_S_le_W y.2
    exact M.W_le_Agrp hyW
  have hrange : Nat.card f.range = 2 := by
    have hR : ∀ g ∈ f.range, g = 1 ∨ g = SL3.zP0 := by
      rintro _ ⟨x, rfl⟩
      refine SL3.R2m_inf_R0 _ (mem_pullL.mp (M.Agrp_le_R2 x.2.1)).2 ?_
      rw [← M.θQ_eq]
      exact ⟨⟨x.1, hle x.2⟩, Subgroup.mem_subgroupOf.mpr (M.Q5_le_Q _ x.2.2), rfl⟩
    have hz : SL3.zP0 ∈ f.range :=
      ⟨⟨M.ael, M.ael_mem_Agrp, M.ael_mem_Q5⟩, M.θ_ael⟩
    rw [Nat.card_eq_two_iff' 1]
    refine ⟨⟨SL3.zP0, hz⟩, fun h => SL3.zP0_ne_one (congrArg Subtype.val h), ?_⟩
    rintro ⟨g, hg⟩ hg1
    rcases hR g hg with rfl | rfl
    · exact absurd rfl hg1
    · rfl
  rw [hker, hrange] at h
  exact h.symm.trans (by norm_num)

theorem card_TF : Nat.card M.TF = 2 ^ 12 := by
  have h := card_sup_mul_inf_of_normalizes M.Agrp_le_normalizer_Q5
  rw [M.card_Agrp_inf_Q5, M.card_Agrp, card_Q5 M.b5el_mem_H M.orderOf_b5el] at h
  have h' : Nat.card ↥(M.Agrp ⊔ M.Q5 M.b5el_mem_H) * 2 ^ 8 = 2 ^ 12 * 2 ^ 8 := by
    rw [h]
    norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

theorem Agrp_inf_B5Q5 :
    M.Agrp ⊓ M.B5Q5 = M.Agrp ⊓ M.Q5 M.b5el_mem_H := by
  refine le_antisymm ?_ (inf_le_inf_left _ le_sup_left)
  rintro x ⟨hxA, hxB⟩
  obtain ⟨q, hq, i, rfl⟩ := M.mem_B5Q5 hxB
  have hqQ := M.Q5_le_Q _ hq
  have hinvA : (q * M.b5el ^ i)⁻¹ ∈ M.Agrp := inv_mem hxA
  have hmem : (q * M.b5el ^ i)⁻¹ * M.b5el ^ i ∈ ruQ M.T := by
    have e : (q * M.b5el ^ i)⁻¹ * M.b5el ^ i = M.b5el ^ (-i) * q⁻¹ * (M.b5el ^ (-i))⁻¹ := by
      group
    rw [e]
    exact M.conj_mem_Q (zpow_mem M.b5el_mem_H _) (inv_mem hqQ)
  obtain ⟨-, hbi⟩ := M.mem_Q_of_mul_zpow_mem_Q (M.Agrp_le_H hinvA)
    (M.pow_eq_one_of_mem_Agrp hinvA) hmem
  rw [hbi, mul_one] at hxA ⊢
  exact ⟨hxA, hq⟩

theorem card_B5Q5 : Nat.card M.B5Q5 = 2 ^ 9 * 5 := by
  have h := card_sup_mul_inf_of_normalizes M.zpowers_le_normalizer_Q5
  have hinf : Subgroup.zpowers M.b5el ⊓ M.Q5 M.b5el_mem_H = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have h1 : orderOf x ∣ 5 := by
      have := Subgroup.orderOf_dvd_natCard _ hx1
      rwa [Nat.card_zpowers, M.orderOf_b5el] at this
    have h2 : orderOf x ∣ 2 ^ 9 := by
      have := Subgroup.orderOf_dvd_natCard _ hx2
      rwa [card_Q5 M.b5el_mem_H M.orderOf_b5el] at this
    have hd := Nat.dvd_gcd h1 h2
    have : Nat.gcd 5 (2 ^ 9) = 1 := by norm_num
    rw [this, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact (Subgroup.mem_bot).mpr hd
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, M.orderOf_b5el,
    card_Q5 M.b5el_mem_H M.orderOf_b5el, sup_comm] at h
  exact h.trans (by norm_num)

theorem card_F1 : Nat.card M.F1 = 2 ^ 12 * 5 := by
  have h := card_sup_mul_inf_of_normalizes M.Agrp_le_normalizer_B5Q5
  rw [M.Agrp_inf_B5Q5, M.card_Agrp_inf_Q5, M.card_Agrp, M.card_B5Q5] at h
  have h' : Nat.card ↥(M.Agrp ⊔ M.B5Q5) * 2 ^ 8 = 2 ^ 12 * 5 * 2 ^ 8 := by
    rw [h]
    norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

end RuDataM

end CFSG.Quasithin.RuType
