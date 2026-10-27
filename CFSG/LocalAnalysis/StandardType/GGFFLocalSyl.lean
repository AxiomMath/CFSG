module

public import CFSG.LocalAnalysis.StandardType.GGFFLocal

@[expose] public section

namespace CFSG.StandardType.GGFF

open CFSG.RankThree.PartTwo.Sec21.FF79 (Cen CenS Nor)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

variable {G : Type} [Group G] [Finite G]

namespace SettingCore

variable {b : G} {K : Subgroup G} {z : Fin 3 → K}

private theorem conjAut_pow_apply {n : G} (hn : ∀ k ∈ K, n * k * n⁻¹ ∈ K) (m : ℕ) (k : K) :
    (((conjAut hn) ^ m) k : G) = n ^ m * (k : G) * (n ^ m)⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', MulAut.mul_apply, conjAut_apply, ih, pow_succ']
    group

private theorem cube_mem_zpowers_of_mem_cenS_Bt (h : SettingCore b K z)
    (hcen : ∀ k : K, (∀ i, k * z i = z i * k) → ∃ v, k = vecElt z v)
    {y : G} (hy : y ∈ CenS (Bt b z)) (hy9 : y ^ 9 = 1) :
    y ^ 3 ∈ Subgroup.zpowers b := by
  have hyCen : y ∈ Cen b :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hy b (b_mem_Bt b z)).symm
  have hn : ∀ k ∈ K, y * k * y⁻¹ ∈ K := h.nor y hyCen
  have hα9 : (conjAut hn) ^ 9 = 1 := by
    refine MulEquiv.ext fun w => Subtype.ext ?_
    rw [conjAut_pow_apply hn 9 w, hy9]
    simp
  obtain ⟨k, hk⟩ := h.model.inner_odd (conjAut hn) 9 (by decide) hα9
  have hk_apply : ∀ w : K, y * (w : G) * y⁻¹ = (k : G) * (w : G) * (k : G)⁻¹ := by
    intro w
    have := congrArg (fun β : MulAut K => ((β w : K) : G)) hk
    simpa [conjAut_apply, MulAut.conj_apply] using this
  set d : G := (k : G)⁻¹ * y with hd
  have hdCen : d ∈ CenS K := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' := hk_apply ⟨w, hw⟩
    have hd_eq : d * w * d⁻¹ = w := by
      rw [hd]
      calc (k : G)⁻¹ * y * w * ((k : G)⁻¹ * y)⁻¹
          = (k : G)⁻¹ * (y * w * y⁻¹) * (k : G) := by group
        _ = (k : G)⁻¹ * ((k : G) * w * (k : G)⁻¹) * (k : G) := by rw [hw']
        _ = w := by group
    have : d * w = w * d := by
      calc d * w = d * w * d⁻¹ * d := by group
        _ = w * d := by rw [hd_eq]
    exact this.symm
  have hk_eq : (k : G) = y * d⁻¹ := by
    have h1 : (k : G) * d = y := by rw [hd]; group
    calc (k : G) = (k : G) * d * d⁻¹ := by group
      _ = y * d⁻¹ := by rw [h1]
  have hyz : ∀ i, y * (z i : G) = (z i : G) * y := fun i =>
    (Subgroup.mem_centralizer_iff.mp hy (zs z i) (zs_mem_Bt b z i)).symm
  have hdz : ∀ i, d * (z i : G) = (z i : G) * d := fun i =>
    (Subgroup.mem_centralizer_iff.mp hdCen (z i) (z i).2).symm
  have hkzi : ∀ i, k * z i = z i * k := by
    intro i
    apply Subtype.ext
    have hdiz : d⁻¹ * (z i : G) = (z i : G) * d⁻¹ := by
      have h := congrArg (fun t => d⁻¹ * t * d⁻¹) (hdz i)
      rw [show d⁻¹ * (d * (z i : G)) * d⁻¹ = (z i : G) * d⁻¹ by group,
          show d⁻¹ * ((z i : G) * d) * d⁻¹ = d⁻¹ * (z i : G) by group] at h
      exact h.symm
    show (k : G) * (z i : G) = (z i : G) * (k : G)
    rw [hk_eq]
    calc (y * d⁻¹) * (z i : G) = y * (d⁻¹ * (z i : G)) := by group
      _ = y * ((z i : G) * d⁻¹) := by rw [hdiz]
      _ = ((z i : G) * y) * d⁻¹ := by rw [← hyz i]; group
      _ = (z i : G) * (y * d⁻¹) := by group
  obtain ⟨v, hv⟩ := hcen k hkzi
  have hk3 : (k : K) ^ 3 = 1 := by
    rw [hv]
    exact h.model.isElemAbelian_tor'.2 (vecElt z v) (vecElt_mem_tor z v)
  have hk3G : (k : G) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hk3, Subgroup.coe_one]
  have hkd : Commute (k : G) d :=
    Subgroup.mem_centralizer_iff.mp hdCen (k : G) (k : K).2
  have h1 : (k : G) * d = y := by rw [hd]; group
  have hy3 : y ^ 3 = d ^ 3 := by
    rw [h1.symm, hkd.mul_pow 3, hk3G, one_mul]
  have hd9 : d ^ 9 = 1 := by
    calc d ^ 9 = (d ^ 3) ^ 3 := by rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul]
      _ = (y ^ 3) ^ 3 := by rw [hy3]
      _ = y ^ 9 := by rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul]
      _ = 1 := hy9
  have hdb : d ∈ Cen b := by
    rw [hd]
    exact (Cen b).mul_mem ((Cen b).inv_mem (h.le (k : K).2)) hyCen
  have hd3b : d ^ 3 ∈ Cen b := (Cen b).pow_mem hdb 3
  have hd3K : d ^ 3 ∈ CenS K := (CenS K).pow_mem hdCen 3
  have hd3cube : (d ^ 3) ^ 3 = 1 := by
    rw [← pow_mul, show (3 : ℕ) * 3 = 9 by norm_num, hd9]
  have hd3mem : d ^ 3 ∈ Subgroup.zpowers b := h.mem_zpowers_of_cube hd3b hd3K hd3cube
  rwa [hy3]

theorem syl (h : SettingCore b K z)
    (hcen : ∀ k : K, (∀ i, k * z i = z i * k) → ∃ v, k = vecElt z v)
    (hN : ¬ Nor (Bt b z) ≤ Nor (Subgroup.zpowers b)) {P : Subgroup G} (hPK : P ≤ CenS K)
    (hPb : P ≤ Cen b) (hP : IsPGroup 3 P) (hbP : Subgroup.zpowers b ≤ P) :
    P = Subgroup.zpowers b := by
  by_contra hne
  have hlt : Subgroup.zpowers b < P := lt_of_le_of_ne hbP (Ne.symm hne)
  have hcardb : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, h.ord]
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hcard_lt : Nat.card (Subgroup.zpowers b) < Nat.card P := Subgroup.card_lt_of_lt hlt
  rw [hcardb, hk] at hcard_lt
  have hk2 : 2 ≤ k := by
    have h1 : (3 : ℕ) ^ 1 < 3 ^ k := by simpa using hcard_lt
    have := (pow_lt_pow_iff_right₀ (show (1 : ℕ) < 3 by norm_num)).mp h1
    omega
  obtain ⟨Q, hQcard, hbQ, hQP⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (p := 3) (n := 2)
    (H := Subgroup.zpowers b) (L := P) (hp := Nat.prime_three)
    (by rw [hcardb]; norm_num) (by rw [hk]; exact pow_dvd_pow 3 hk2) hbP
  have hcycP : IsCyclic P := h.cyc P hPK hP
  have hcycQ : IsCyclic Q := Subgroup.isCyclic_of_le hQP
  obtain ⟨gQ, hgQ⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcycQ
  have horder_gQ : orderOf gQ = 9 := by
    rw [orderOf_eq_card_of_zpowers_eq_top hgQ, hQcard]
    norm_num
  set q : G := (gQ : G) with hq
  have horder_q : orderOf q = 9 := by rw [hq, Subgroup.orderOf_coe, horder_gQ]
  have hqQ : q ∈ Q := by rw [hq]; exact gQ.2
  have hqP : q ∈ P := hQP hqQ
  have hqCenb : q ∈ Cen b := hPb hqP
  have hqCenK : q ∈ CenS K := hPK hqP
  have hbQ' : b ∈ Q := hbQ (Subgroup.mem_zpowers b)
  have hq3Q : q ^ 3 ∈ Q := Q.pow_mem hqQ 3
  have hHcard1 : Nat.card ((Subgroup.zpowers b).subgroupOf Q) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hbQ).toEquiv, Nat.card_zpowers, h.ord]
  have hHcard2 : Nat.card ((Subgroup.zpowers (q ^ 3)).subgroupOf Q) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hq3Q)).toEquiv,
      Nat.card_zpowers, orderOf_pow, horder_q]
    norm_num
  have hH : (Subgroup.zpowers b).subgroupOf Q = (Subgroup.zpowers (q ^ 3)).subgroupOf Q :=
    (IsCyclic.subgroup_eq_iff_card_eq).mpr (by rw [hHcard1, hHcard2])
  have hb_mem_q3 : b ∈ Subgroup.zpowers (q ^ 3) := by
    have h1 : (⟨b, hbQ'⟩ : Q) ∈ (Subgroup.zpowers b).subgroupOf Q :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers b)
    rw [hH] at h1
    simpa using Subgroup.mem_subgroupOf.mp h1
  have hqCenS_Bt : q ∈ CenS (Bt b z) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨j, v, rfl⟩ := h.mem_Bt.mp hx
    have hcq_b : Commute q (b ^ j) :=
      Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hqCenb) j
    have hcq_v : Commute q (vecElt (zs z) v) :=
      (Subgroup.mem_centralizer_iff.mp hqCenK (vecElt (zs z) v)
        (tor_le z (vecElt_mem_tor _ v))).symm
    exact (hcq_b.mul_right hcq_v).eq.symm
  have hq9 : q ^ 9 = 1 := by
    rw [← horder_q]
    exact pow_orderOf_eq_one q
  refine hN ?_
  intro n hn
  refine mem_nor_of_conj_mem fun x hx => ?_
  have hzpow_le : Subgroup.zpowers b ≤ Subgroup.zpowers (q ^ 3) :=
    Subgroup.zpowers_le.mpr hb_mem_q3
  have hx' : x ∈ Subgroup.zpowers (q ^ 3) := hzpow_le hx
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx'
  have hyCenS : n * q * n⁻¹ ∈ CenS (Bt b z) := by
    rw [Subgroup.mem_centralizer_iff] at hqCenS_Bt ⊢
    intro x hx
    have hxn : n⁻¹ * x * n ∈ Bt b z := by
      have hn' : n⁻¹ ∈ Nor (Bt b z) := (Nor (Bt b z)).inv_mem hn
      simpa using ((Subgroup.mem_normalizer_iff.mp hn' x).mp hx)
    have hcomm := hqCenS_Bt (n⁻¹ * x * n) hxn
    calc x * (n * q * n⁻¹) = n * ((n⁻¹ * x * n) * q) * n⁻¹ := by group
      _ = n * (q * (n⁻¹ * x * n)) * n⁻¹ := by rw [hcomm]
      _ = (n * q * n⁻¹) * x := by group
  have hy9 : (n * q * n⁻¹) ^ 9 = 1 := by
    have e : (n * q * n⁻¹) ^ 9 = n * q ^ 9 * n⁻¹ := by
      change (MulAut.conj n q) ^ 9 = MulAut.conj n (q ^ 9)
      rw [map_pow]
    rw [e, hq9]
    group
  have hstep := cube_mem_zpowers_of_mem_cenS_Bt h hcen hyCenS hy9
  have hkey : n * q ^ 3 * n⁻¹ ∈ Subgroup.zpowers b := by
    have e : (n * q * n⁻¹) ^ 3 = n * q ^ 3 * n⁻¹ := by
      change (MulAut.conj n q) ^ 3 = MulAut.conj n (q ^ 3)
      rw [map_pow]
    rwa [e] at hstep
  have e2 : n * (q ^ 3) ^ j * n⁻¹ = (n * q ^ 3 * n⁻¹) ^ j := by
    change (MulAut.conj n) ((q ^ 3) ^ j) = (MulAut.conj n (q ^ 3)) ^ j
    rw [map_zpow]
  have hmem : (n * q ^ 3 * n⁻¹) ^ j ∈ Subgroup.zpowers b :=
    Subgroup.zpowers_le.mpr hkey (Subgroup.zpow_mem_zpowers _ j)
  rwa [← hj, e2]

end SettingCore

end CFSG.StandardType.GGFF

end
