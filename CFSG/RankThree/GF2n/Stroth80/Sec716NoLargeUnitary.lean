module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmtUnRoot
import CFSG.RankThree.GF2n.Stroth80.Sec716PpdExclusion
import CFSG.RankThree.GF2n.Stroth80.Sec83NatSection
import CFSG.LieType.Universal.Unitary.LongRootCentralizer
public import CFSG.RankThree.GF2n.Stroth80.Sec12Cases

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n.Tim81 CFSG.Timmesfeld CFSG.Timmesfeld.ARS
open CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Bridge
open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_lift_order_comm [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {t : G}
    (ht : t ∈ LB M Q B) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {ybar : Hbar M Q Z}
    (horder : orderOf ybar = r)
    (hcomm : ∀ v ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), Commute ybar v) :
    ∃ y : G, orderOf y = r ∧ y ∈ H0 M Z ∧
      ∀ z ∈ Z0, y * z * y⁻¹ * z⁻¹ ∈ Q := by
  classical
  have hZ0H0 : Z0 ≤ H0 M Z := hZ0.le.trans (hc.Rt_le_H0 t)
  have hQ2 : IsPGroup 2 ↥Q := by
    rw [hc.hyp.hQ]
    exact (inSubgroup_pCore_two M).1
  have hN : ∀ n ∈ Q.subgroupOf M, ∃ k : ℕ, n ^ 2 ^ k = 1 := by
    intro n hn
    obtain ⟨k, hk⟩ := hQ2 ⟨(n : G), Subgroup.mem_subgroupOf.mp hn⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  obtain ⟨rEl, hro, _, hrz⟩ :=
    exists_lift_orderOf (R := M) (N := Q.subgroupOf M) hN (ybar : Mbar M Q) (by
      rw [Subgroup.orderOf_coe, horder]
      exact hr.odd_of_ne_two hr2)
  have hyH : (rEl : G) ∈ H0 M Z :=
    (mk_mem_bar_iff_sec4 hc.Q_le_H0 rEl).mp ((Subgroup.zpowers_le.mpr ybar.2) hrz)
  refine ⟨(rEl : G), ?_, hyH, ?_⟩
  · calc orderOf ((rEl : G)) = orderOf rEl := Subgroup.orderOf_coe rEl
      _ = orderOf (ybar : Mbar M Q) := hro
      _ = orderOf ybar := Subgroup.orderOf_coe ybar
      _ = r := horder
  · intro z hzZ0
    let zM : ↥M := ⟨z, (hZ0H0.trans inf_le_left) hzZ0⟩
    have hmemZ0 : QuotientGroup.mk' (Q.subgroupOf M) zM ∈ bar M Q Z0 :=
      (mk_mem_bar_iff_sec4 (hc.Q_le_centre ht hZ0) zM).mpr hzZ0
    have hmemH0' : QuotientGroup.mk' (Q.subgroupOf M) zM ∈ bar M Q (H0 M Z) :=
      (Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
        fun w hw => hZ0H0 hw) hmemZ0
    have hcommH : Commute (ybar : Mbar M Q) (QuotientGroup.mk' (Q.subgroupOf M) zM) :=
      (hcomm ⟨QuotientGroup.mk' (Q.subgroupOf M) zM, hmemH0'⟩ hmemZ0).map
        (Subgroup.subtype (bar M Q (H0 M Z)))
    have hcommM : Commute (QuotientGroup.mk' (Q.subgroupOf M) rEl)
        (QuotientGroup.mk' (Q.subgroupOf M) zM) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hrz
      rw [← hk]
      exact hcommH.zpow_left k
    simpa [commutatorElement_def] using
      (mk_commute_iff (M := M) (Q := Q) rEl zM).mp hcommM

theorem ppd_card_data {q qQ qZ0 n v : ℕ} {f l m r : ℕ} (hf : 2 ≤ f)
    (hq : q = 2 ^ f) (hm : 6 ≤ m) (hlm : l + 3 < m)
    (hV : v = q ^ (2 * l + 1)) (hN : n = qQ * q ^ (2 * m - 3))
    (hZ0 : qZ0 = qQ * q) (hppd : IsPrimitivePrimeDivisor r (2 * f * (m - 3))) :
    v = q * 2 ^ (2 * l * f) ∧ n = qZ0 * 2 ^ ((2 * m - 4) * f) ∧
      (∀ i, 0 < i → i ≤ 2 * l * f → ¬ r ∣ 2 ^ i - 1) ∧
      ¬ r ∣ 2 ^ ((2 * m - 4) * f) - 1 ∧ r ≠ 2 := by
  have hkpos : 0 < 2 * f * (m - 3) := by
    have hf0 : 0 < f := by omega
    have h3 : 0 < m - 3 := by omega
    positivity
  have hV' : v = q * 2 ^ (2 * l * f) := by
    rw [hV, hq, ← pow_mul, ← pow_add]
    congr 1
    ring
  have hNZ' : n = qZ0 * q ^ (2 * m - 4) := by
    rw [hN, hZ0, show 2 * m - 3 = 2 * m - 4 + 1 by omega, pow_succ]
    ring
  have hNZ : n = qZ0 * 2 ^ ((2 * m - 4) * f) := by
    rw [hNZ', hq, ← pow_mul, Nat.mul_comm f (2 * m - 4)]
  have hrj : ∀ i, 0 < i → i ≤ 2 * l * f → ¬ r ∣ 2 ^ i - 1 := by
    intro i hi hile
    refine hppd.2.2 i hi ?_
    have h1 : l < m - 3 := by omega
    have h2 : 2 * l * f < 2 * f * (m - 3) := by
      calc 2 * l * f < 2 * (m - 3) * f :=
            Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left h1 (by norm_num))
              (by omega : 0 < f)
        _ = 2 * f * (m - 3) := by ring
    exact lt_of_le_of_lt hile h2
  have hre : ¬ r ∣ 2 ^ ((2 * m - 4) * f) - 1 := by
    rw [hppd.dvd_sub_one_iff hkpos]
    intro hdvd
    have h2m : 2 * m - 4 = 2 * (m - 2) := by omega
    rw [h2m] at hdvd
    have hdvd' : 2 * f * (m - 3) ∣ 2 * f * (m - 2) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hdvd
    have hdvd'' : m - 3 ∣ m - 2 :=
      Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < 2 * f) hdvd'
    have h1 : m - 3 ∣ 1 := by
      have := Nat.dvd_sub hdvd'' (dvd_refl (m - 3))
      simpa [show m - 2 - (m - 3) = 1 by omega] using this
    have hle : m - 3 ≤ 1 := Nat.le_of_dvd (by norm_num) h1
    omega
  exact ⟨hV', hNZ, hrj, hre, hppd.ne_two hkpos⟩

theorem exp_eq_of_card_CN (hc : Ctx M Q Z B) {t : G} {a b : ℕ}
    (ha : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ a)
    (hb : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ b) : a = b := by
  have h1 : Nat.card Z ^ a = Nat.card Z ^ b := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Q))
    rw [← ha, hb]
  exact Nat.pow_right_injective (by have := hc.hyp.q4; omega) h1

theorem not_unitaryRootAt_of_card [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {t : G} (ht : t ∈ LB M Q B) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hirr : IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0)
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)))
    (hst : ∀ s ∈ Z0, s ∉ Q → Rt M (LB M Q B) s = Rt M (LB M Q B) t ∧
      Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t)
    (hZ0card : Nat.card Z0 = Nat.card Q * Nat.card Z)
    {l m : ℕ} (hlm : l + 3 < m) (hm : 6 ≤ m) (he : Even m)
    (hV : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ (2 * l + 1))
    (hk : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ (2 * m - 3)) :
    ¬ UnitaryRootAt M Q Z Z0 m := by
  classical
  rintro ⟨f, hf, hZq, hm4, Φ, hΦ, x, hx⟩
  obtain ⟨r, ybar, hppd, horder, hcomm⟩ :=
    exists_ppd_commute_map_conjSub hf hm he Φ hΦ x
  rw [← hx] at hcomm
  obtain ⟨hV', hNZ, hrj, hre, hr2⟩ :=
    ppd_card_data (q := Nat.card Z) (qQ := Nat.card Q) (qZ0 := Nat.card Z0)
      (n := Nat.card ↥(hc.CN t)) (v := Nat.card ↥(Vt M (LB M Q B) B Z t))
      (f := f) (l := l) (m := m) (r := r) hf hZq hm hlm hV hk hZ0card hppd
  have hr : r.Prime := hppd.prime
  obtain ⟨y, hy, hyH, hyZ0⟩ :=
    exists_lift_order_comm hc ht hZ0 hr hr2 horder hcomm
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0ne : ∃ s ∈ Z0, s ∉ Q := by
    refine SetLike.exists_of_lt (lt_of_le_of_ne hQZ0 fun h => ?_)
    have hcard : Nat.card Q = Nat.card Q * Nat.card Z := by
      rw [← hZ0card]
      exact congrArg (fun S : Subgroup G => Nat.card ↥S) h
    have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
    nlinarith [hcard, hq2, Nat.card_pos (α := Q)]
  obtain ⟨hyR, hyV⟩ := conj_Rt_Vt_of_centre_eq hc ht hZ0 hst hZ0ne hyH hyZ0
  have hQ2 : IsPGroup 2 ↥Q := by
    rw [hc.hyp.hQ]
    exact (inSubgroup_pCore_two M).1
  have hZ0two : IsPGroup 2 ↥Z0 := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hQ2
    refine IsPGroup.of_card (n := a + f) ?_
    rw [hZ0card, ha, hZq, pow_add]
  exact false_of_ppd_centralizing_Z0 hc ht hZ0 hirr hF hV' hNZ hr hr2 hrj hre hyH hy
    hyZ0 hyR hyV hZ0two

theorem not_unitaryRootAt_of_orth [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {t : G}
    (ht : t ∈ LB M Q B) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hirr : IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0)
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)))
    (hst : ∀ s ∈ Z0, s ∉ Q → Rt M (LB M Q B) s = Rt M (LB M Q B) t ∧
      Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t)
    (hZ0card : Nat.card Z0 = Nat.card Q * Nat.card Z)
    {l m : ℕ} (hl : 1 ≤ l) (hor : OmegaPlusNat hc t l ∨ OmegaMinusNat hc t l)
    (hlm : l + 3 < m) (hm : 6 ≤ m) (he : Even m)
    (hk : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ (2 * m - 3)) :
    ¬ UnitaryRootAt M Q Z Z0 m := by
  have hV : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ (2 * l + 1) := by
    rcases hor with hplus | hminus
    · exact card_Vt_of_plus hplus
    · exact card_Vt_of_minus hl hminus
  exact not_unitaryRootAt_of_card hc ht hZ0 hirr hF hst hZ0card hlm hm he hV hk

theorem not_unitaryRootAt_sec7 (h78 : Stroth78Statement) (hZt : Sec7ZtStatement)
    (hZcard : Sec7ZCardStatement) [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hirr : IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0)
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)))
    {m : ℕ} (hm : 6 < m) (hk : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ (2 * m - 3)) :
    ¬ UnitaryRootAt M Q Z Z0 m := by
  obtain ⟨l, hl2, hor⟩ := hs.orth
  have hst : ∀ s ∈ Z0, s ∉ Q → Rt M (LB M Q B) s = Rt M (LB M Q B) t ∧
      Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t :=
    fun s hsZ0 hsQ => hZt G M Q Z B hc n t hs Z0 hZ0 s hsZ0 hsQ
  have hZ0card : Nat.card Z0 = Nat.card Q * Nat.card Z :=
    hZcard G M Q Z B hc n t hs Z0 hZ0
  rcases h78 G M Q Z B hc n t hs.toSec5 hs.large hs.notPlus4 l hl2 hor with
    ⟨-, -, hcard⟩ | ⟨hl4, -, hcard⟩ | ⟨-, -, -, hcard⟩ | ⟨hl5, -, -, hcard⟩ |
      ⟨hl6, -, -, hcard⟩
  · have := exp_eq_of_card_CN hc hcard hk
    omega
  · have hm10 : m = 10 := by have := exp_eq_of_card_CN hc hcard hk; omega
    subst hl4
    exact not_unitaryRootAt_of_orth (m := m) hc hs.toSec5.mem hZ0 hirr hF hst hZ0card
      (by omega) hor (by omega) (by omega) (by rw [hm10]; norm_num) hk
  · have := exp_eq_of_card_CN hc hcard hk
    omega
  · have hm10 : m = 10 := by have := exp_eq_of_card_CN hc hcard hk; omega
    subst hl5
    exact not_unitaryRootAt_of_orth (m := m) hc hs.toSec5.mem hZ0 hirr hF hst hZ0card
      (by omega) hor (by omega) (by omega) (by rw [hm10]; norm_num) hk
  · have hm18 : m = 18 := by have := exp_eq_of_card_CN hc hcard hk; omega
    subst hl6
    exact not_unitaryRootAt_of_orth (m := m) hc hs.toSec5.mem hZ0 hirr hF hst hZ0card
      (by omega) hor (by omega) (by omega) (by rw [hm18]; norm_num) hk

theorem not_unitaryRootAt_sec8 (h83 : Stroth83Statement) (hZt : Sec8ZtStatement)
    (hZcard : Sec86ZCardStatement) [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hirr : IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0)
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)))
    {m : ℕ} (hm : 6 < m) (hk : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ (2 * m - 3)) :
    ¬ UnitaryRootAt M Q Z Z0 m := by
  have hst : ∀ s ∈ Z0, s ∉ Q → Rt M (LB M Q B) s = Rt M (LB M Q B) t ∧
      Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t :=
    fun s hsZ0 hsQ => hZt G M Q Z B hc n t hs Z0 hZ0 s hsZ0 hsQ
  have hZ0card : Nat.card Z0 = Nat.card Q * Nat.card Z :=
    hZcard G M Q Z B hc n t hs Z0 hZ0
  rcases h83 G M Q Z B hc n t hs.toSec5 hs.sp with ⟨-, hsp3, hcard⟩ | ⟨-, hsp4, hcard⟩
  · have := exp_eq_of_card_CN hc hcard hk
    omega
  · have hm10 : m = 10 := by have := exp_eq_of_card_CN hc hcard hk; omega
    exact not_unitaryRootAt_of_card (l := 4) (m := m) hc hs.toSec5.mem hZ0 hirr hF hst
      hZ0card (by omega) (by omega) (by rw [hm10]; norm_num) hsp4.card_V hk

theorem sec716NoLargeUnitaryRoot_of (h78 : Stroth78Statement) (hZt : Sec7ZtStatement)
    (hZcard : Sec7ZCardStatement) : Sec716NoLargeUnitaryRootStatement :=
  fun _ _ _ _ _ _ _ _ hc _ _ hs _ hZ0 hirr hF _ hm hk =>
    not_unitaryRootAt_sec7 h78 hZt hZcard hc hs hZ0 hirr hF hm hk

theorem sec86NoLargeUnitaryRoot_of (h83 : Stroth83Statement) (hZt : Sec8ZtStatement)
    (hZcard : Sec86ZCardStatement) : Sec86NoLargeUnitaryRootStatement :=
  fun _ _ _ _ _ _ _ _ hc _ _ hs _ hZ0 hirr hF _ hm hk =>
    not_unitaryRootAt_sec8 h83 hZt hZcard hc hs hZ0 hirr hF hm hk

end CFSG.RankThree.GF2n.Stroth80
