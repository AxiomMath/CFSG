module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.Setup
import CFSG.LocalAnalysis.StandardType.FF81.LocalSetupCen

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

private theorem conjAut_pow_apply {G : Type} [Group G] [Finite G] {K : Subgroup G} {n : G}
    (hn : ∀ k ∈ K, n * k * n⁻¹ ∈ K) (m : ℕ) (k : K) :
    (((GGFF.conjAut hn) ^ m) k : G) = n ^ m * (k : G) * (n ^ m)⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', MulAut.mul_apply, GGFF.conjAut_apply, ih, pow_succ']
    group

theorem mem_Bt_of_isPGroup_cen {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) :
    ∀ x ∈ cB b z, IsPGroup 3 (Subgroup.zpowers x) → x ∈ GGFF.Bt b z := by
  intro x hx hxpg
  have hS : GGFF.SettingCore b L z := h.settingCore
  have hxBmem : x ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hx b (GGFF.SettingCore.b_mem_Bt b z)).symm
  have hxL : x ∈ Subgroup.normalizer (L : Set G) := h.hypA.nor hxBmem
  have hconj : ∀ k ∈ L, x * k * x⁻¹ ∈ L := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp hxL k).mp hk
  obtain ⟨a, ha⟩ := hxpg ⟨x, Subgroup.mem_zpowers x⟩
  have hxa : x ^ (3 ^ a) = 1 := by
    simpa using congrArg (fun w : Subgroup.zpowers x => (w : G)) ha
  rcases Nat.eq_zero_or_pos a with rfl | hapos
  · rw [pow_zero, pow_one] at hxa
    rw [hxa]
    exact (GGFF.Bt b z).one_mem
  · set α : MulAut ↥L := GGFF.conjAut hconj with hαdef
    have hαm : α ^ (3 ^ a) = 1 := by
      refine MulEquiv.ext fun w => Subtype.ext ?_
      rw [conjAut_pow_apply hconj (3 ^ a) w, hxa]
      simp
    have hodd : Odd (3 ^ a) := (show Odd 3 by norm_num).pow
    obtain ⟨l, hl⟩ := h.model.inner_odd α (3 ^ a) hodd hαm
    set y : G := (l : G)⁻¹ * x with hydef
    have hylcomm : ∀ k : ↥L, y * (k : G) * y⁻¹ = (k : G) := by
      intro k
      have hk := congrArg (fun β : MulAut ↥L => ((β k : ↥L) : G)) hl
      have hxk : ((α k : ↥L) : G) = x * (k : G) * x⁻¹ := by
        simp only [hαdef, GGFF.conjAut_apply]
      have hlk : ((MulAut.conj l k : ↥L) : G) = (l : G) * (k : G) * (l : G)⁻¹ := by
        simp [MulAut.conj_apply]
      rw [hxk, hlk] at hk
      calc y * (k : G) * y⁻¹
          = (l : G)⁻¹ * (x * (k : G) * x⁻¹) * (l : G) := by rw [hydef]; group
        _ = (l : G)⁻¹ * ((l : G) * (k : G) * (l : G)⁻¹) * (l : G) := by rw [hk]
        _ = (k : G) := by group
    have hxzi : ∀ i, x * GGFF.zs z i * x⁻¹ = GGFF.zs z i := by
      intro i
      have hc := Subgroup.mem_centralizer_iff.mp hx (GGFF.zs z i)
        (GGFF.SettingCore.zs_mem_Bt b z i)
      rw [← hc]; group
    have hlzi : ∀ i, (l : G) * GGFF.zs z i * (l : G)⁻¹ = GGFF.zs z i := by
      intro i
      have hyi : y * GGFF.zs z i * y⁻¹ = GGFF.zs z i := hylcomm (z i)
      have hyeq : y⁻¹ * GGFF.zs z i * y = GGFF.zs z i := by
        have h2 : y * GGFF.zs z i = GGFF.zs z i * y := by
          calc y * GGFF.zs z i = y * GGFF.zs z i * y⁻¹ * y := by group
            _ = GGFF.zs z i * y := by rw [hyi]
        calc y⁻¹ * GGFF.zs z i * y = y⁻¹ * (GGFF.zs z i * y) := by group
          _ = y⁻¹ * (y * GGFF.zs z i) := by rw [← h2]
          _ = GGFF.zs z i := by group
      have hxl : (l : G) = x * y⁻¹ := by rw [hydef]; group
      calc (l : G) * GGFF.zs z i * (l : G)⁻¹
          = x * y⁻¹ * GGFF.zs z i * (x * y⁻¹)⁻¹ := by rw [hxl]
        _ = x * (y⁻¹ * GGFF.zs z i * y) * x⁻¹ := by group
        _ = x * GGFF.zs z i * x⁻¹ := by rw [hyeq]
        _ = GGFF.zs z i := hxzi i
    have hlcomm : ∀ i, l * z i = z i * l := by
      intro i
      apply Subtype.ext
      have h := hlzi i
      have h2 : (l : G) * (z i : G) = (z i : G) * (l : G) := by
        calc (l : G) * (z i : G) = (l : G) * (z i : G) * (l : G)⁻¹ * (l : G) := by
              group
          _ = (z i : G) * (l : G) := by rw [h]
      simpa only [Subgroup.coe_mul] using h2
    obtain ⟨v, hv⟩ :=
      CFSG.StandardType.FF81.cen_of_model h.hypA.n_cases h.hypA.model h.model l hlcomm
    have hlB : (l : G) ∈ GGFF.tor (GGFF.zs z) := by
      rw [congrArg Subtype.val hv, ← GGFF.SettingCore.vecElt_zs z v]
      exact GGFF.vecElt_mem_tor (GGFF.zs z) v
    have hl3 : (l : G) ^ 3 = 1 :=
      (GGFF.isElemAbelian_tor hS.zs_pow hS.zs_comm).2 (l : G) hlB
    have hlpow : (l : G) ^ (3 ^ a) = 1 := by
      have hdvd : orderOf (l : G) ∣ 3 ^ a :=
        (orderOf_dvd_of_pow_eq_one hl3).trans (dvd_pow_self 3 (by omega))
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    have hlCen : (l : G) ∈ Subgroup.centralizer ({b} : Set G) := h.hypA.le l.2
    have hlBt : (l : G) ∈ GGFF.Bt b z := GGFF.SettingCore.tor_le_Bt b z hlB
    have hlxComm : Commute (l : G) x :=
      Subgroup.mem_centralizer_iff.mp hx (l : G) hlBt
    have hyPow : y ^ (3 ^ a) = 1 := by
      rw [hydef, hlxComm.inv_left.mul_pow]
      simp [hlpow, hxa]
    have hyb : y ∈ Subgroup.centralizer ({b} : Set G) :=
      (Subgroup.centralizer ({b} : Set G)).mul_mem
        ((Subgroup.centralizer ({b} : Set G)).inv_mem hlCen) hxBmem
    have hzn : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
      refine Subgroup.zpowers_le.mpr ?_
      refine Subgroup.mem_normalizer_iff.mpr fun q => ?_
      have hcomm_yb : Commute y b := Subgroup.mem_centralizer_singleton_iff.mp hyb
      have hbcomm : ∀ j : ℤ, b * y ^ j = y ^ j * b := fun j =>
        (Commute.zpow_left hcomm_yb j).eq.symm
      constructor
      · intro hq
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
        rw [hbcomm j]
        simp
      · intro hq
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hq
        have hbcomm' : b⁻¹ * y ^ j * b = y ^ j := by
          calc b⁻¹ * y ^ j * b = b⁻¹ * (b * y ^ j) := by
                rw [hbcomm j]; group
            _ = y ^ j := by group
        have hqeq : q = y ^ j := by
          calc q = b⁻¹ * (b * q * b⁻¹) * b := by group
            _ = b⁻¹ * y ^ j * b := by rw [hj]
            _ = y ^ j := hbcomm'
        rw [hqeq]
        exact Subgroup.zpow_mem_zpowers y j
    have hP3 : IsPGroup 3 (Subgroup.zpowers b ⊔ Subgroup.zpowers y : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right'
        (IsPGroup.of_card_dvd_pow (n := 1) (by rw [Nat.card_zpowers, hS.ord]; norm_num))
        (IsPGroup.of_card_dvd_pow (n := a) (by
          rw [Nat.card_zpowers]
          exact orderOf_dvd_of_pow_eq_one hyPow)) hzn
    have hPL : Subgroup.zpowers b ⊔ Subgroup.zpowers y ≤
        Subgroup.centralizer (L : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr hS.b_mem_cenS) (Subgroup.zpowers_le.mpr ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h := hylcomm ⟨k, hk⟩
      have h2 : y * k = k * y := by
        calc y * k = y * k * y⁻¹ * y := by group
          _ = k * y := by rw [h]
      exact h2.symm
    have hPb : Subgroup.zpowers b ⊔ Subgroup.zpowers y ≤
        Subgroup.centralizer ({b} : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
        (Subgroup.zpowers_le.mpr hyb)
    have hPsyl := h.facts.syl _ hPL hPb hP3 (le_sup_left : Subgroup.zpowers b ≤ _)
    have hyP : y ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers y :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    have hyZp : y ∈ Subgroup.zpowers b := hPsyl ▸ hyP
    have hxeq : x = (l : G) * y := by rw [hydef]; group
    rw [hxeq]
    exact (GGFF.Bt b z).mul_mem (GGFF.SettingCore.tor_le_Bt b z hlB)
      (Subgroup.mem_sup_left hyZp)

theorem exists_cen_complement {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) :
    ∃ Y : Subgroup G, Y ≤ cB b z ∧ ¬ 3 ∣ Nat.card Y ∧
      (∀ x ∈ cB b z, ∃ w ∈ GGFF.Bt b z, ∃ y ∈ Y, x = w * y) ∧
      ∀ m ∈ nB b z, ∀ y ∈ Y, m * y * m⁻¹ ∈ Y := by
  have hS : GGFF.SettingCore b L z := h.settingCore
  let H : Subgroup G := cB b z
  have hBleH : GGFF.Bt b z ≤ H := by
    intro x hx
    show x ∈ cB b z
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hS.isElemAbelian_Bt.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  let B' : Subgroup H := (GGFF.Bt b z).subgroupOf H
  have hB'card : Nat.card B' = 81 := by
    have hmap : Nat.card (B'.map H.subtype) = Nat.card B' :=
      Subgroup.card_map_of_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hBleH, hS.card_Bt] at hmap
    exact hmap.symm
  have hB'p : IsPGroup 3 B' := IsPGroup.of_card (n := 4) (by rw [hB'card]; norm_num)
  have hB'max : ∀ {Q : Subgroup H}, IsPGroup 3 Q → B' ≤ Q → Q = B' := by
    intro Q hQ hle
    refine le_antisymm ?_ hle
    intro q hq
    have hq3H : IsPGroup 3 (Subgroup.zpowers q) := hQ.to_le (Subgroup.zpowers_le.mpr hq)
    have hq3 : IsPGroup 3 (Subgroup.zpowers ((q : H) : G)) := by
      have h2 := hq3H.map H.subtype
      rwa [MonoidHom.map_zpowers] at h2
    have hqBt : ((q : H) : G) ∈ GGFF.Bt b z :=
      mem_Bt_of_isPGroup_cen h ((q : H) : G) q.2 hq3
    exact Subgroup.mem_subgroupOf.mpr hqBt
  let P : Sylow 3 H :=
    { toSubgroup := B'
      isPGroup' := hB'p
      is_maximal' := fun {_} hQ hle => hB'max hQ hle }
  have hPcen : ∀ p ∈ (P : Subgroup H), ∀ m : H, m * p = p * m := by
    intro p hp m
    have hpBt : ((p : H) : G) ∈ GGFF.Bt b z := Subgroup.mem_subgroupOf.mp hp
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp m.2 ((p : H) : G) hpBt).symm
  have hPnorm : Subgroup.normalizer (P : Set H) ≤ Subgroup.centralizer (P : Set H) := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (hPcen p hp m).symm
  let K : Subgroup H := (MonoidHom.transferSylow P hPnorm).ker
  have hcomp : Subgroup.IsComplement' K (P : Subgroup H) :=
    letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    letI : Finite (Sylow 3 H) := Sylow.finite_of_finiteIndex P
    MonoidHom.ker_transferSylow_isComplement' P hPnorm
  have hKnotdvd : ¬ 3 ∣ Nat.card K :=
    letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    letI : Finite (Sylow 3 H) := Sylow.finite_of_finiteIndex P
    MonoidHom.not_dvd_card_ker_transferSylow P hPnorm
  let Y : Subgroup G := K.map H.subtype
  have hYle : Y ≤ cB b z := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact k.2
  have hYcard : Nat.card Y = Nat.card K :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hYnotdvd : ¬ 3 ∣ Nat.card Y := by rw [hYcard]; exact hKnotdvd
  have hY3' : ∀ y ∈ Y, ¬ 3 ∣ orderOf y := by
    intro y hy h3
    obtain ⟨k, hk, rfl⟩ := hy
    have hord : orderOf (H.subtype k) = orderOf k :=
      orderOf_injective H.subtype H.subtype_injective k
    have h3' : 3 ∣ orderOf k := by simpa only [hord] using h3
    exact hKnotdvd (h3'.trans (Subgroup.orderOf_dvd_natCard K hk))
  have hdecomp : ∀ x ∈ cB b z, ∃ w ∈ GGFF.Bt b z, ∃ y ∈ Y, x = w * y := by
    intro x hx
    obtain ⟨⟨k, p⟩, hkp⟩ := hcomp.2 (⟨x, hx⟩ : H)
    have hkpG : ((k : H) : G) * ((p : H) : G) = x := by
      simpa using congrArg Subtype.val hkp
    have hpkG : ((p : H) : G) * ((k : H) : G) = ((k : H) : G) * ((p : H) : G) :=
      (congrArg Subtype.val (hPcen p p.2 k)).symm
    refine ⟨((p : H) : G), Subgroup.mem_subgroupOf.mp p.2, ((k : H) : G),
      Subgroup.mem_map.mpr ⟨k, k.2, rfl⟩, ?_⟩
    rw [← hkpG]
    exact hpkG.symm
  have hYchar : ∀ x ∈ cB b z, ¬ 3 ∣ orderOf x → x ∈ Y := by
    intro x hx hx3
    obtain ⟨w, hw, y, hy, rfl⟩ := hdecomp x hx
    have hwc : Commute w y := Subgroup.mem_centralizer_iff.mp (hYle hy) w hw
    set s : ℕ := orderOf y with hs
    have hs3 : ¬ 3 ∣ s := hY3' y hy
    have hws : w ^ s = 1 := by
      have h1 : orderOf (w ^ s) ∣ 3 := by
        rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul,
          show s * 3 = 3 * s by omega, pow_mul, hS.isElemAbelian_Bt.2 w hw, one_pow]
      have hxs : (w * y) ^ s = w ^ s := by
        rw [hwc.mul_pow, hs, pow_orderOf_eq_one, mul_one]
      have h2 : orderOf (w ^ s) ∣ orderOf (w * y) := by
        rw [← hxs]
        exact orderOf_pow_dvd (x := w * y) s
      have hnot3 : ¬ 3 ∣ orderOf (w ^ s) := fun h3 => hx3 (h3.trans h2)
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h1 with h | h
      · exact orderOf_eq_one_iff.mp h
      · exfalso
        exact hnot3 (h ▸ dvd_rfl)
    have hw3 : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one (hS.isElemAbelian_Bt.2 w hw)
    have hwsdvd : orderOf w ∣ s := orderOf_dvd_of_pow_eq_one hws
    have hone : orderOf w = 1 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hw3 with h | h
      · exact h
      · exfalso
        exact hs3 (h ▸ hwsdvd)
    have hw1 : w = 1 := orderOf_eq_one_iff.mp hone
    rw [hw1, one_mul]
    exact hy
  refine ⟨Y, hYle, hYnotdvd, hdecomp, ?_⟩
  intro m hm y hy
  have hord : orderOf (m * y * m⁻¹) = orderOf y := by
    have hc := MulEquiv.orderOf_eq (MulAut.conj m) y
    simpa [MulAut.conj_apply] using hc
  have hnot3 : ¬ 3 ∣ orderOf (m * y * m⁻¹) := by
    rw [hord]; exact hY3' y hy
  refine hYchar (m * y * m⁻¹) ?_ hnot3
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hu : m⁻¹ * w * m ∈ GGFF.Bt b z := by
    have h := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer ((GGFF.Bt b z : Subgroup G) : Set G)).inv_mem hm) w).mp hw
    simpa using h
  have hyu : y * (m⁻¹ * w * m) = (m⁻¹ * w * m) * y :=
    (Subgroup.mem_centralizer_iff.mp (hYle hy) (m⁻¹ * w * m) hu).symm
  have hconj : m * y * m⁻¹ * w = w * (m * y * m⁻¹) := by
    calc m * y * m⁻¹ * w = m * y * (m⁻¹ * w * m) * m⁻¹ := by group
      _ = m * (y * (m⁻¹ * w * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * w * m) * y) * m⁻¹ := by rw [hyu]
      _ = w * (m * y * m⁻¹) := by group
  exact hconj.symm


end CFSG.StandardType.FF81.PropOne

end
