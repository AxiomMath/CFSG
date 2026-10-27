module

public import CFSG.Quasithin.EmptyFaithful.S152ZA
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.Quasithin.EmptyFaithful.T1515Der

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Z2

omit [Finite G] in
theorem le_normalizer_commutator {H P Q : Subgroup G}
    (hHP : H ≤ Subgroup.normalizer (P : Set G)) (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) :
    H ≤ Subgroup.normalizer ((⁅P, Q⁆ : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHP hh),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHQ hh)]

theorem opResidual_yOf152 (T Mc M : Subgroup G) :
    opResidual 2 (yOf152 T Mc M) = yOf152 T Mc M := by
  have h := opResidual_two_oTwoUpper1516 (yOf152 T Mc M)
  rw [← yOf152_eq_oTwoUpper T Mc M] at h
  exact h

end Z2

namespace YCtx

variable {T Mc M : Subgroup G} (c : YCtx T Mc M)

include c

theorem exists_five :
    ∃ y ∈ yOf152 T Mc M, orderOf y = 5 ∧ ∀ x ∈ yOf152 T Mc M, ∃ k : ℤ,
      (y ^ k)⁻¹ * x ∈ pCoreOf 2 (yOf152 T Mc M) := by
  set Y := yOf152 T Mc M with hY
  have h5 : (pCoreOf 2 Y).relIndex Y = 5 := c.relIndex_five
  have hdvd : 5 ∣ Nat.card ↥Y := h5 ▸ Subgroup.relIndex_dvd_card _ _
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' 5 hdvd
  refine ⟨(y₀ : G), y₀.2, by rw [Subgroup.orderOf_coe]; exact hy₀, ?_⟩
  have hy₀Q : (y₀ : G) ∉ pCoreOf 2 Y := by
    intro hmem
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 Y) ⟨(y₀ : G), hmem⟩
    have h1 : y₀ ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h5d : 5 ∣ 2 ^ k := hy₀ ▸ orderOf_dvd_of_pow_eq_one h1
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5d
    omega
  let N : Subgroup ↥Y := (pCoreOf 2 Y).subgroupOf Y
  have hN : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_pCoreOf 2 Y)
  have hcard : Nat.card (↥Y ⧸ N) = 5 := h5
  have hne : (QuotientGroup.mk y₀ : ↥Y ⧸ N) ≠ 1 := fun h =>
    hy₀Q (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff y₀).mp h))
  have htop := zpowers_eq_top_of_prime_card hcard hne
  intro x hx
  have hmem : (QuotientGroup.mk ⟨x, hx⟩ : ↥Y ⧸ N) ∈ Subgroup.zpowers (QuotientGroup.mk y₀) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq] at hk
  exact Subgroup.mem_subgroupOf.mp hk

end YCtx

namespace Ctx15204

variable {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5} (c : Ctx15204 T Mc M H K₁ K₂ π)

include c

theorem charTwo_Mc : CharTwo Mc := by
  have hq := c.hs.qtfe
  have hT : IsSylowTwoOf T ⊤ := isSylowTwoOf_of_le151 hq.sylow le_top
  exact charTwo_of_isTwoLocal_of_isSylowTwoOf_le hq.qtke.2.1 hT hq.mc_max.1 hq.t_le_mc

theorem S_le_Mc : sOf T K₁ ≤ Mc := S_le_T.trans c.hs.qtfe.t_le_mc

theorem S_le_Mc_inf : sOf T K₁ ≤ Mc ⊓ g0Of T Mc M K₁ := le_inf c.S_le_Mc S_le_G₀

theorem charTwo_Mc_inf : CharTwo (Mc ⊓ g0Of T Mc M K₁) := by
  have hTMc : IsSylowTwoOf T Mc := isSylowTwoOf_of_le151 c.hs.qtfe.sylow c.hs.qtfe.t_le_mc
  refine charTwo_of_relIndex_le_two c.charTwo_Mc hTMc inf_le_left ?_
  have h1 : (Mc ⊓ g0Of T Mc M K₁).relIndex T ∣ (sOf T K₁).relIndex T :=
    Subgroup.relIndex_dvd_of_le_left T c.S_le_Mc_inf
  have h2 : (sOf T K₁).relIndex T = 2 := c.wr.relIndex_S c.hT
  rw [h2] at h1
  exact Nat.le_of_dvd (by norm_num) h1

theorem V_isElemAbelian : IsElemAbelian 2 (V154 T Mc M) := S152N.isElemAbelian_V154 c.hs

theorem V_le_M : V154 T Mc M ≤ M :=
  (Subgroup.le_normalizer : V154 T Mc M ≤ Subgroup.normalizer (V154 T Mc M : Set G)).trans
    (S152N.normalizer_V154_eq c.hs).le

theorem V_le_normalizer_Y : V154 T Mc M ≤ Subgroup.normalizer (yOf152 T Mc M : Set G) :=
  c.V_le_M.trans c.y.normal

theorem T_le_normalizer_V : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
  c.y.data.T_le.trans c.y.hMV

theorem commV_le_pCoreY : ⁅V154 T Mc M, yOf152 T Mc M⁆ ≤ pCoreOf 2 (yOf152 T Mc M) := by
  have h1 : ⁅V154 T Mc M, yOf152 T Mc M⁆ ≤ V154 T Mc M :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp c.y.hYV
  have h2 : ⁅V154 T Mc M, yOf152 T Mc M⁆ ≤ yOf152 T Mc M := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp c.V_le_normalizer_Y
  rw [c.y.pCoreY_eq]
  refine le_inf h2 fun x hx => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have := c.V_isElemAbelian.1
  exact congrArg Subtype.val (mul_comm' (⟨v, hv⟩ : V154 T Mc M) ⟨x, h1 hx⟩)

theorem commV_ne_bot : ⁅V154 T Mc M, yOf152 T Mc M⁆ ≠ ⊥ := by
  intro h
  have h1 : yOf152 T Mc M ≤ Subgroup.centralizer (V154 T Mc M : Set G) := by
    rw [Subgroup.commutator_comm] at h
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have h2 : pCoreOf 2 (yOf152 T Mc M) = yOf152 T Mc M := by
    rw [c.y.pCoreY_eq]
    exact inf_eq_left.mpr h1
  have h3 := c.y.relIndex_five
  rw [h2, Subgroup.relIndex_self] at h3
  omega

theorem commV_idem :
    ⁅⁅V154 T Mc M, yOf152 T Mc M⁆, yOf152 T Mc M⁆ = ⁅V154 T Mc M, yOf152 T Mc M⁆ := by
  obtain ⟨y, hyY, hy5, hdec⟩ := c.y.exists_five
  set V := V154 T Mc M with hV
  set Y := yOf152 T Mc M with hY
  set P : Subgroup G := Subgroup.zpowers y with hP
  have hPY : P ≤ Y := Subgroup.zpowers_le.mpr hyY
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hPY.trans c.y.hYV
  have hPp : IsPGroup 5 P :=
    IsPGroup.of_card (n := 1) (by rw [hP, Nat.card_zpowers, hy5]; norm_num)
  have hVp : IsPGroup 2 V := isPGroup_of_isElemAbelian c.V_isElemAbelian
  have hcop : ¬ 5 ∣ Nat.card V := by
    obtain ⟨n, hn⟩ := hVp.exists_card_eq
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h
    omega
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 5
    (by norm_num) P V hPp hcop hPN
  have hQV : pCoreOf 2 Y ≤ Subgroup.centralizer (V : Set G) := by
    rw [c.y.pCoreY_eq]
    exact inf_le_right
  have hVY_le : ⁅V, Y⁆ ≤ ⁅V, P⁆ := by
    refine Subgroup.commutator_le.mpr fun v hv x hx => ?_
    obtain ⟨k, hk⟩ := hdec x hx
    obtain ⟨o, ho⟩ : ∃ o, o = (y ^ k)⁻¹ * x := ⟨_, rfl⟩
    rw [← ho] at hk
    have hxo : x = y ^ k * o := by rw [ho]; group
    have hoV := Subgroup.mem_centralizer_iff.mp (hQV hk)
    have hc : o * v⁻¹ = v⁻¹ * o := (hoV v⁻¹ (V.inv_mem hv)).symm
    have h1 : ⁅v, x⁆ = ⁅v, y ^ k⁆ := by
      rw [hxo, commutatorElement_def, commutatorElement_def]
      calc v * (y ^ k * o) * v⁻¹ * (y ^ k * o)⁻¹
          = v * y ^ k * (o * v⁻¹ * o⁻¹) * (y ^ k)⁻¹ := by group
        _ = v * y ^ k * v⁻¹ * (y ^ k)⁻¹ := by rw [hc]; group
    rw [h1]
    exact Subgroup.commutator_mem_commutator hv (Subgroup.zpow_mem_zpowers y k)
  have hVY_eq : ⁅V, Y⁆ = ⁅V, P⁆ := le_antisymm hVY_le (Subgroup.commutator_mono le_rfl hPY)
  have hnormY : Y ≤ Subgroup.normalizer ((⁅V, Y⁆ : Subgroup G) : Set G) :=
    Z2.le_normalizer_commutator c.y.hYV Subgroup.le_normalizer
  apply le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp hnormY)
  calc ⁅V, Y⁆ = ⁅V, P⁆ := hVY_eq
    _ = ⁅⁅V, P⁆, P⁆ := hidem.symm
    _ = ⁅⁅V, Y⁆, P⁆ := by rw [hVY_eq]
    _ ≤ ⁅⁅V, Y⁆, Y⁆ := Subgroup.commutator_mono le_rfl hPY

theorem oddCoreIn_G₀_eq_bot (hne : pCoreOf 2 (g0Of T Mc M K₁) ≠ ⊥) :
    oddCoreIn (g0Of T Mc M K₁) = ⊥ := by
  have hq := c.hs.qtfe
  set V := V154 T Mc M with hV
  set Y := yOf152 T Mc M with hY
  have h1 : ⁅V, Y⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp c.y.hYV
  have hV₀S : ⁅V, Y⁆ ≤ sOf T K₁ := c.commV_le_pCoreY.trans c.pCoreY_le_S
  have hV₀G : ⁅V, Y⁆ ≤ g0Of T Mc M K₁ := hV₀S.trans S_le_G₀
  have hV₀T : ⁅V, Y⁆ ≤ T := hV₀S.trans S_le_T
  have hTV₀ : T ≤ Subgroup.normalizer ((⁅V, Y⁆ : Subgroup G) : Set G) :=
    Z2.le_normalizer_commutator c.T_le_normalizer_V c.T_le_normalizer_Y
  obtain ⟨z, hzV₀, hz1, hzZ⟩ :=
    exists_ne_one_mem_omegaOneCenter_of_normalized hq.sylow.1 hV₀T c.commV_ne_bot hTV₀
  have hzm := mem_quasithinOmegaOneCenter_iff.mp hzZ
  have hzc : Subgroup.centralizer ({z} : Set G) ≤ Mc :=
    centralizer_singleton_le_mc_of_mem_omegaOneCenter hq hzZ hz1
  have h := confined_involution_inverts_oddCoreIn c.charTwo_Mc_inf inf_le_right (hV₀G hzV₀)
    hzm.2.2 (fun x hx => ⟨hzc hx.2, hx.1⟩)
  have hel : IsElemAbelian 2 (⁅V, Y⁆ : Subgroup G) := isElemAbelian_mono151 h1 c.V_isElemAbelian
  have hcent := a126_one Y_le_G₀ (Z2.opResidual_yOf152 T Mc M) hV₀G (isPGroup_of_isElemAbelian hel)
    c.commV_idem (pRank_pCoreOf_le_two1516 hq hne) (C2Nine.frattiniIn_eq_bot_of_isElemAbelian hel)
  refine eq_bot_iff.mpr fun y hy => ?_
  have hyz : y ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact (Subgroup.mem_centralizer_iff.mp (hcent hzV₀) y hy).symm
  have hmem : y ∈ oddCoreIn (g0Of T Mc M K₁) ⊓ Subgroup.centralizer ({z} : Set G) := ⟨hy, hyz⟩
  rw [h.2.1] at hmem
  exact hmem

end Ctx15204

end CFSG.Quasithin.He9
