module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT2Klein
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT2Sec

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

section Local

variable (F : Frame L1 L2 S D X)
include F

theorem no_transvection_Zv {x : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = false)
    (hZF : ZFaithful x) {a : G} (ha : a ∈ stab x) (haQ : a ∉ Qv x) (ha2 : a ^ 2 ∈ Qv x)
    {k : ℕ} (hak : a ^ 2 ^ k = 1) :
    ¬ (Zv x ⊓ Subgroup.centralizer ({a} : Set G)).relIndex (Zv x) ≤ 2 := by
  intro hidx2
  have hA := Amal.of_frame F
  have h5 : ∀ y ∈ stab x, y ^ 5 = 1 → y ∈ Subgroup.centralizer (Zv x : Set G) :=
    fun y hy hy5 => five_centralizes_of_transvection F hx (hA.isElemAbelian_Zv x)
      (hA.stab_le_normalizer_Zv x) (Qv_le_centralizer_Zv F x) ha haQ ha2 hidx2 hy hy5
  have hZ : ZCentral x := fun T hT => Zv_eq_omega_of_five F hx h5 hT
  obtain ⟨T0, hT0, -⟩ := hA.exists_sylow_stab x
  have hPgrp : IsPGroup 2 (Subgroup.zpowers a) := by
    intro y
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp y.2
    refine ⟨k, ?_⟩
    apply Subtype.ext
    have : (y : G) ^ 2 ^ k = 1 := by
      rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hak, one_zpow]
    simpa using this
  have hPH : Subgroup.zpowers a ≤ stab x := Subgroup.zpowers_le.mpr ha
  obtain ⟨g, hg, hPle⟩ := isSylowTwoOf_exists_conj_le hT0 hPH hPgrp
  have hT : IsSylowTwoOf (conjSub g T0) (stab x) := by
    have h := isSylowTwoOf_conj hT0 g
    rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hg)] at h
  have haT : a ∈ conjSub g T0 := hPle (Subgroup.mem_zpowers a)
  have haC : a ∈ Subgroup.centralizer (Zv x : Set G) := centralizes_Zv_of_zcentral hZ hT haT
  have haQ' : a ∈ conjSub g T0 ⊓ Subgroup.centralizer (Zv x : Set G) :=
    Subgroup.mem_inf.mpr ⟨haT, haC⟩
  rw [hZF _ hT] at haQ'
  exact haQ haQ'

theorem false_of_Vn_le_Zv {w x : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hw : vtype w = true)
    (hxw : x ∈ nbrs w) (hMx : Vn w ≤ Zv x) : False := by
  have hA := Amal.of_frame F
  have hxw' : (graph _ _ _).Adj w x := hxw
  have hall : ∀ p ∈ nbrs w, Zv p = Zv x := by
    intro p hp
    obtain ⟨g, -, hgx⟩ := exists_stab_smul_nbr F hw hxw hp
    have h1 : Zv p ≤ Zv x := (hA.Zv_le_Vn hp).trans hMx
    have h2 : Zv p = conjSub (g : G) (Zv x) := by
      calc Zv p = Zv (g • x) := by rw [hgx]
        _ = conjSub (g : G) (Zv x) := Zv_smul _ _
    exact Subgroup.eq_of_le_of_card_ge h1 (by rw [h2]; exact (card_conjSub (g : G) (Zv x)).ge)
  have hnp : stab w ≤ Subgroup.normalizer (Zv x : Set G) := by
    intro k hk
    obtain ⟨hG0, hfix⟩ := mem_stab.mp hk
    have hku : (⟨k, hG0⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) • x ∈ nbrs w := by
      have := (smul_adj (⟨k, hG0⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S))).mpr hxw'
      rwa [hfix] at this
    have e := Zv_smul (⟨k, hG0⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) x
    rw [hall _ hku] at e
    exact mem_normalizer_of_conjSub_eq e.symm
  have hwx : w ∈ nbrs x := hxw'.symm
  have hU : Zv x ≤ stab w ⊓ stab x :=
    le_inf ((Zv_le_Qv_of_mem_nbrs F hwx).trans (pCoreOf_le 2 _))
      ((hA.Zv_le_Qv x).trans (pCoreOf_le 2 _))
  exact hA.Zv_ne_bot x (hA.eq_bot_of_normalizes_both hxw' hU hnp (hA.stab_le_normalizer_Zv x))

theorem exists_third_v {w γ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hw : vtype w = true)
    (hγ : γ ∈ nbrs w) {y : G} (hy : y ∈ Qv γ) (hyQ : y ∉ Qv w) :
    ∃ q ∈ Qv γ, q ∉ Qv w ∧ y * q ∉ Qv w := by
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  obtain ⟨h, hh1, hh0⟩ := exists_edge_conj_true hw hγ
  have hQγ : Qv γ = conjSub (h : G) (Q1 L1 L2 S) := by
    rw [← hh0, Qv_smul]; unfold Qv; rw [stab_γ₀ h₁]
  have hQw : Qv w = conjSub (h : G) (Q2 L1 L2 S) := by
    rw [← hh1, Qv_smul]; unfold Qv; rw [stab_γ₁ h₂]
  have hy1 : (h : G)⁻¹ * y * h ∈ Q1 L1 L2 S := by rw [hQγ] at hy; exact mem_conjSub.mp hy
  have hy2 : (h : G)⁻¹ * y * h ∉ Q2 L1 L2 S := by
    intro h'; apply hyQ; rw [hQw]; exact mem_conjSub.mpr h'
  obtain ⟨q, hq1, hq2, hyq, -⟩ := exists_third F hy1 hy2
  refine ⟨(h : G) * q * (h : G)⁻¹, ?_, ?_, ?_⟩
  · rw [hQγ, mem_conjSub]; simpa [mul_assoc] using hq1
  · rw [hQw, mem_conjSub]; simpa [mul_assoc] using hq2
  · rw [hQw, mem_conjSub]
    have e : (h : G)⁻¹ * (y * ((h : G) * q * (h : G)⁻¹)) * h = ((h : G)⁻¹ * y * h) * q := by group
    rw [e]; exact hyq


theorem claim1 {w x : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hw : vtype w = true) (hxw : x ∈ nbrs w) :
    ∃ g ∈ stab w, ∃ y ∈ Vn w, g * y * g⁻¹ * y⁻¹ ∉ ⁅Vn w, Qv w⁆ := by
  have hA := Amal.of_frame F
  by_contra hcon
  push Not at hcon
  have hMQ : Vn w ≤ Qv w := iSup₂_le fun μ hμ =>
    Zv_le_Qv_of_mem_nbrs F ((show (graph _ _ _).Adj w μ from hμ).symm)
  have hHQ : Qv w ≤ Subgroup.normalizer (Zv x : Set G) := fun g hg =>
    hA.stab_le_normalizer_Zv x (hA.Qv_le_stab_of_mem_nbrs hxw hg)
  have hle : Vn w ≤ Zv x ⊔ ⁅Vn w, Qv w⁆ := by
    refine iSup₂_le fun p hp => ?_
    obtain ⟨g, hg, hgx⟩ := exists_stab_smul_nbr F hw hxw hp
    have hZp : Zv p = conjSub (g : G) (Zv x) := by
      calc Zv p = Zv (g • x) := by rw [hgx]
        _ = conjSub (g : G) (Zv x) := Zv_smul _ _
    intro y hy
    rw [hZp, mem_conjSub] at hy
    have hu : (g : G)⁻¹ * y * (g : G) ∈ Vn w := hA.Zv_le_Vn hxw hy
    have h1 := hcon g hg _ hu
    have e : y = ((g : G) * ((g : G)⁻¹ * y * (g : G)) * (g : G)⁻¹ * ((g : G)⁻¹ * y * (g : G))⁻¹) *
        ((g : G)⁻¹ * y * (g : G)) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hy)
  have hMx : Vn w ≤ Zv x :=
    le_of_le_sup_commutator (pCoreOf_isPGroup 2 (stab w) : IsPGroup 2 (Qv w)) hMQ hHQ hle
  exact false_of_Vn_le_Zv F hw hxw hMx

theorem comm_mem_Qv {w γ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hw : vtype w = true)
    (hγ : γ ∈ nbrs w) {a b : G} (ha : a ∈ Qv γ) (hb : b ∈ Qv γ) :
    a * b * a⁻¹ * b⁻¹ ∈ Qv w := by
  have hA := Amal.of_frame F
  have hwγ : w ∈ nbrs γ := (show (graph _ _ _).Adj w γ from hγ).symm
  have h4 := relIndex_Qv_sup_Qv F hw hγ
  set Y : Subgroup G := Qv γ ⊔ Qv w with hY
  have hQγs : Qv γ ≤ stab w := fun g hg => hA.Qv_le_stab_of_mem_nbrs hwγ hg
  have hYle : Y ≤ stab w := sup_le hQγs (pCoreOf_le 2 _)
  have hQw : Qv w ≤ Y := le_sup_right
  have hKn : ((Qv w).subgroupOf Y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : ((g : ↥Y) : G) ∈ stab w := hYle g.2
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab w) hg) _).mp hn
  have hcard : Nat.card (↥Y ⧸ (Qv w).subgroupOf Y) = 2 ^ 2 := by
    rw [← Subgroup.index_eq_card]
    show (Qv w).relIndex Y = 2 ^ 2
    rw [h4]; norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hcard
  let a' : ↥Y := ⟨a, Subgroup.mem_sup_left ha⟩
  let b' : ↥Y := ⟨b, Subgroup.mem_sup_left hb⟩
  have h1 : (QuotientGroup.mk' ((Qv w).subgroupOf Y)) ⁅a', b'⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (IsMulCommutative.is_comm.comm _ _)
  have h2 : ⁅a', b'⁆ ∈ (Qv w).subgroupOf Y := (QuotientGroup.eq_one_iff _).mp h1
  rw [Subgroup.mem_subgroupOf] at h2
  simpa [commutatorElement_def] using h2

end Local


theorem relIndex_ne_zero_G (H K : Subgroup G) : H.relIndex K ≠ 0 := by
  unfold Subgroup.relIndex; exact Subgroup.index_ne_zero_of_finite

theorem NT_of_relIndex (F : Frame L1 L2 S D X) {w γ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hw : vtype w = true)
    (hγ : γ ∈ nbrs w) (hγf : vtype γ = false) (hZFγ : ZFaithful γ) (C' Pg : Subgroup G)
    (hC'rel : (Zv γ ⊓ C').relIndex (Zv γ) ≤ 2)
    (hPcent : ∀ s ∈ Pg, ∀ c ∈ C', s * c = c * s) (hPle : Pg ≤ stab w)
    (hPnorm : ∀ p ∈ Pg, ∀ t ∈ stab w, t * p * t⁻¹ ∈ Pg)
    (hPtrans : ∀ x' ∈ nbrs w, ∃ p ∈ Pg, ∃ hp : p ∈ P1 L1 L2 S ⊔ P2 L1 L2 S,
      (⟨p, hp⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) • γ = x') :
    ∀ x' ∈ nbrs w, Qv w ⊓ Qv x' = Qv w ⊓ Qv γ := by
  have hA := Amal.of_frame F
  have hPG : IsPGroup 2 ↥(Qv γ ⊔ Qv w) := by
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 (stab w) : IsPGroup 2 (Qv w)).exists_card_eq
    have h4 := relIndex_Qv_sup_Qv F hw hγ
    have h5 := Subgroup.relIndex_mul_card (H := Qv w) (K := Qv γ ⊔ Qv w)
    rw [inf_eq_left.mpr le_sup_right, h4] at h5
    rw [show Nat.card ↥(Qv w) = 2 ^ m from hm] at h5
    exact IsPGroup.of_card (n := m + 2) (by rw [← h5]; ring)
  have hQγle : Qv γ ⊔ Qv w ≤ stab γ :=
    sup_le (pCoreOf_le 2 _) (hA.Qv_le_stab_of_mem_nbrs hγ)
  have hDstep : ∀ s ∈ Qv γ ⊔ Qv w, s ∈ Pg → s ∈ Qv γ := by
    intro s hsY hsP
    by_contra hsQ
    obtain ⟨k, hk⟩ := hPG ⟨s, hsY⟩
    have hk1 : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨j, hjQ, hj2⟩ := exists_pow_sq_mem (Qv γ) hsQ (n := k)
      (by rw [hk1]; exact (Qv γ).one_mem)
    have hsj : s ^ j ∈ Qv γ ⊔ Qv w := Subgroup.pow_mem _ hsY j
    obtain ⟨k', hk'⟩ := hPG ⟨s ^ j, hsj⟩
    have hk'1 : (s ^ j) ^ 2 ^ k' = 1 := by simpa using congrArg Subtype.val hk'
    have hsub : Zv γ ⊓ C' ≤ Zv γ ⊓ Subgroup.centralizer ({s ^ j} : Set G) := by
      refine le_inf inf_le_left fun c hc => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hPcent _ (Subgroup.pow_mem _ hsP j) c (Subgroup.mem_inf.mp hc).2
    have hle := (Subgroup.relIndex_le_of_le_left hsub (relIndex_ne_zero_G _ _)).trans hC'rel
    exact no_transvection_Zv F hγf hZFγ (hQγle hsj) hjQ (by rw [pow_two]; exact hj2) hk'1 hle
  have hT : ∀ p ∈ Pg, ∀ t ∈ Qv w ⊓ Qv γ, p * t * p⁻¹ ∈ Qv w ⊓ Qv γ := by
    intro p hp t ht
    obtain ⟨htw, htγ⟩ := Subgroup.mem_inf.mp ht
    have hts : t ∈ stab w := pCoreOf_le 2 _ htw
    have hpw : p * t * p⁻¹ ∈ Qv w :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab w) (hPle hp)) t).mp htw
    have hc : p * t * p⁻¹ * t⁻¹ ∈ Pg := by
      have := Pg.mul_mem hp (hPnorm p⁻¹ (Pg.inv_mem hp) t hts)
      simpa [mul_assoc] using this
    have hcw : p * t * p⁻¹ * t⁻¹ ∈ Qv w := (Qv w).mul_mem hpw ((Qv w).inv_mem htw)
    have hcγ : p * t * p⁻¹ * t⁻¹ ∈ Qv γ := hDstep _ (Subgroup.mem_sup_right hcw) hc
    have : p * t * p⁻¹ = (p * t * p⁻¹ * t⁻¹) * t := by group
    rw [this]
    exact (Qv w ⊓ Qv γ).mul_mem (Subgroup.mem_inf.mpr ⟨hcw, hcγ⟩) ht
  intro x' hx'
  obtain ⟨p, hpP, hp, hpx⟩ := hPtrans x' hx'
  have hQx' : Qv x' = conjSub p (Qv γ) := by
    rw [← hpx, Qv_smul]
  have hQw : Qv w = conjSub p (Qv w) :=
    (conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 (stab w) (hPle hpP))).symm
  ext t
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hQx']
  have hpinv : p⁻¹ ∈ stab w := hPle (Pg.inv_mem hpP)
  constructor
  · rintro ⟨htw, htx⟩
    rw [mem_conjSub] at htx
    have h1 : p⁻¹ * t * p ∈ Qv w := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab w) hpinv) t).mp htw
      rw [inv_inv] at this
      exact this
    have h2 := hT p hpP _ (Subgroup.mem_inf.mpr ⟨h1, htx⟩)
    have e : p * (p⁻¹ * t * p) * p⁻¹ = t := by group
    rw [e] at h2
    exact ⟨htw, (Subgroup.mem_inf.mp h2).2⟩
  · rintro ⟨htw, htγ⟩
    refine ⟨htw, ?_⟩
    rw [mem_conjSub]
    have h2 := hT p⁻¹ (Pg.inv_mem hpP) t (Subgroup.mem_inf.mpr ⟨htw, htγ⟩)
    simpa using (Subgroup.mem_inf.mp h2).2

section Core

open CFSG.Quasithin.Kleidman.F204.Sec

variable (F : Frame L1 L2 S D X) (hb3 : 3 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S))
  (hZ : ∀ μ : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype μ = true → Zv μ ≤ centerOf (stab μ))
include F hb3 hZ

theorem core_geo {w γ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hw : vtype w = true)
    (hγ : γ ∈ nbrs w) (hγf : vtype γ = false) (hZFγ : ZFaithful γ)
    {z : G} (hzγ : z ∈ Qv γ) (hzQ : z ∉ Qv w) (hz2 : z * z = 1) :
    4 ≤ (Vn w ⊓ Subgroup.centralizer ({z} : Set G)).relIndex (Vn w) ∧
    ((Vn w ⊓ Subgroup.centralizer ({z} : Set G)).relIndex (Vn w) ≤ 4 →
      ∀ x' ∈ nbrs w, Qv w ⊓ Qv x' = Qv w ⊓ Qv γ) := by
  have hA := Amal.of_frame F
  have hMab := hA.isElemAbelian_Vn hb3 w
  let cg : CommGroup ↥(Vn w) := { (inferInstance : Group ↥(Vn w)) with
    mul_comm := fun u v => Subtype.ext (isElemAbelian_comm hMab u.2 v.2) }
  have hΓ : stab w ≤ Subgroup.normalizer (Vn w : Set G) := Amal.stab_le_normalizer_Vn' w
  obtain ⟨φ, hφs, hφk⟩ := exists_phi_stab F hw
  let ρ : ↥(stab w) →* MulAut ↥(Vn w) := (Vn w).normalizerMonoidHom.comp (Subgroup.inclusion hΓ)
  have hρ : ∀ (g : ↥(stab w)) (a : ↥(Vn w)), (((ρ g a : ↥(Vn w))) : G) = (g : G) * a * (g : G)⁻¹ :=
    fun g a => Subgroup.normalizerMonoidHom_apply_apply_coe (Vn w) (Subgroup.inclusion hΓ g) a
  have hφk' : ∀ g : ↥(stab w), φ g = 1 ↔ (g : G) ∈ Qv w := by
    intro g
    rw [← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]
  have hQ1 : ∀ Y : Subgroup ↥(Vn w), (qcomm ρ φ.ker Y).map (Vn w).subtype ≤
      ⁅Y.map (Vn w).subtype, Qv w⁆ := by
    intro Y
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    have hqQ : (q : G) ∈ Qv w := (hφk' q).mp hq
    have e : ((ρ q y * y⁻¹ : ↥(Vn w)) : G) = ⁅(q : G), (y : G)⁆ := by
      rw [Subgroup.coe_mul, hρ, Subgroup.coe_inv, commutatorElement_def]
    show ((ρ q y * y⁻¹ : ↥(Vn w)) : G) ∈ _
    rw [e, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hqQ (Subgroup.mem_map_of_mem _ hy)
  have hQ2 : ⁅Vn w, Qv w⁆ ≤ (qcomm ρ φ.ker ⊤).map (Vn w).subtype := by
    rw [Subgroup.commutator_le]
    intro m hm q hq
    have hqs : q ∈ stab w := pCoreOf_le 2 _ hq
    refine ⟨(ρ ⟨q, hqs⟩ ⟨m, hm⟩ * (⟨m, hm⟩ : ↥(Vn w))⁻¹)⁻¹, ?_, ?_⟩
    · exact Subgroup.inv_mem _ (mul_inv_mem_qcomm (K := φ.ker)
        ((hφk' ⟨q, hqs⟩).mpr hq) (Subgroup.mem_top _))
    · show (((ρ ⟨q, hqs⟩ ⟨m, hm⟩ * (⟨m, hm⟩ : ↥(Vn w))⁻¹)⁻¹ : ↥(Vn w)) : G) = _
      rw [Subgroup.coe_inv, Subgroup.coe_mul, hρ, Subgroup.coe_inv, commutatorElement_def]
      group
  have hT : GInv ρ (⊤ : Subgroup ↥(Vn w)) := fun _ _ _ => Subgroup.mem_top _
  have hW : GInv ρ (qcomm ρ φ.ker ⊤) := qcomm_ginv hT
  have h2 : ∀ a : ↥(Vn w), a * a = 1 := fun a => Subtype.ext (by
    have := hMab.2 a a.2
    simpa [sq] using this)
  have hzs : z ∈ stab w := hA.Qv_le_stab_of_mem_nbrs
    ((show (graph _ _ _).Adj w γ from hγ).symm) hzγ
  let zq : ↥(stab w) := ⟨z, hzs⟩
  have hφ1 : φ zq ≠ 1 := fun h => hzQ ((hφk' zq).mp h)
  have hφ2 : φ zq ^ 2 = 1 := by
    rw [← map_pow]
    have : zq ^ 2 = 1 := Subtype.ext (by simpa [sq] using hz2)
    rw [this, map_one]
  have hnt : ∃ (g : ↥(stab w)) (y : ↥(Vn w)), ρ g y * y⁻¹ ∉ qcomm ρ φ.ker ⊤ := by
    obtain ⟨g, hg, y, hy, hnot⟩ := claim1 F hw hγ
    refine ⟨⟨g, hg⟩, ⟨y, hy⟩, fun hmem => hnot ?_⟩
    have h1 : ((ρ ⟨g, hg⟩ ⟨y, hy⟩ * (⟨y, hy⟩ : ↥(Vn w))⁻¹ : ↥(Vn w)) : G) ∈
        (qcomm ρ φ.ker ⊤).map (Vn w).subtype := ⟨_, hmem, rfl⟩
    have h2' := hQ1 ⊤ h1
    rw [Subgroup.map_top, Subgroup.range_subtype] at h2'
    have e : ((ρ ⟨g, hg⟩ ⟨y, hy⟩ * (⟨y, hy⟩ : ↥(Vn w))⁻¹ : ↥(Vn w)) : G) = g * y * g⁻¹ * y⁻¹ := by
      rw [Subgroup.coe_mul, hρ, Subgroup.coe_inv]
    rw [e] at h2'
    exact h2'
  have h4 := four_le_idx_section h2 φ hφs (qcomm_le hT) hT hW
    (fun q hq y _ => mul_inv_mem_qcomm hq (Subgroup.mem_top _))
    (by obtain ⟨g, y, hy⟩ := hnt; exact ⟨g, y, Subgroup.mem_top _, hy⟩) hφ1 hφ2
  have h5 : 4 ≤ idx (ρ zq) ⊤ ⊥ := h4.trans (idx_anti_right _ ⊤ bot_le)
  have h6 : idx (ρ zq) ⊤ ⊥ = (Vn w ⊓ Subgroup.centralizer ({z} : Set G)).relIndex (Vn w) := by
    have hI : I (ρ zq) ⊤ ⊥ =
        (Vn w ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf (Vn w) := by
      ext a
      rw [mem_I, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
        Subgroup.mem_bot, mul_inv_eq_one]
      constructor
      · rintro ⟨-, h⟩
        have h' := congrArg (fun v : ↥(Vn w) => (v : G)) h
        simp only [hρ] at h'
        refine ⟨a.2, fun y0 hy0 => ?_⟩
        rw [Set.mem_singleton_iff] at hy0
        rw [hy0]
        calc z * (a : G) = (z * a * z⁻¹) * z := by group
          _ = (a : G) * z := by rw [show z * (a : G) * z⁻¹ = a from h']
      · rintro ⟨-, h⟩
        refine ⟨Subgroup.mem_top _, Subtype.ext ?_⟩
        rw [hρ]
        have := h z (Set.mem_singleton _)
        show z * (a : G) * z⁻¹ = a
        rw [this]; group
    unfold idx
    rw [hI, Subgroup.relIndex_top_right]
    rfl
  refine ⟨by rw [← h6]; exact h5, fun hbound => ?_⟩
  have hbound' : idx (ρ zq) ⊤ ⊥ ≤ 4 := by rw [h6]; exact hbound
  have hMQ : Vn w ≤ Qv w := iSup₂_le fun μ hμ =>
    Zv_le_Qv_of_mem_nbrs F ((show (graph _ _ _).Adj w μ from hμ).symm)
  have hnil : ∀ Y : Subgroup ↥(Vn w), GInv ρ Y → qcomm ρ φ.ker Y = Y → Y = ⊥ := by
    intro Y _ hY
    have h1 : Y.map (Vn w).subtype ≤ ⁅Y.map (Vn w).subtype, Qv w⁆ := by
      have := hQ1 Y; rw [hY] at this; exact this
    have hYM : Y.map (Vn w).subtype ≤ Qv w := by
      rintro g ⟨y, -, rfl⟩; exact hMQ y.2
    have hHQ : Qv w ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
      rw [Subgroup.normalizer_eq_top]; exact le_top
    have h2' := le_of_le_sup_commutator (pCoreOf_isPGroup 2 (stab w) : IsPGroup 2 (Qv w)) hYM hHQ
      (le_sup_of_le_right h1)
    rw [eq_bot_iff]
    intro y hy
    have : ((y : ↥(Vn w)) : G) ∈ (⊥ : Subgroup G) := h2' ⟨y, hy, rfl⟩
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp this))
  let gm : ↥(stab w) → ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := fun g => ⟨g, stab_le _ g.2⟩
  have hgm_nbr : ∀ (g : ↥(stab w)) (x : ↥(nbrs w)), gm g • x.1 ∈ nbrs w := fun g x => by
    have := (smul_adj (gm g)).mpr (show (graph _ _ _).Adj w x.1 from x.2)
    rwa [smul_eq_of_mem_stab (g := gm g) g.2] at this
  let actΩ : MulAction ↥(stab w) ↥(nbrs w) :=
    { smul := fun g x => ⟨gm g • x.1, hgm_nbr g x⟩
      one_smul := fun x => Subtype.ext (one_smul _ x.1)
      mul_smul := fun g h x => Subtype.ext (mul_smul (gm g) (gm h) x.1) }
  have hsmulΩ : ∀ (g : ↥(stab w)) (x : ↥(nbrs w)), ((g • x : ↥(nbrs w)) : Geo _ _) = gm g • x.1 :=
    fun g x => rfl
  have : MulAction.IsPretransitive ↥(stab w) ↥(nbrs w) := ⟨fun x y => by
    obtain ⟨q, hq, hqx⟩ := exists_stab_smul_nbr F hw x.2 y.2
    exact ⟨⟨q, hq⟩, Subtype.ext hqx⟩⟩
  classical
  have : Fintype ↥(nbrs w) := Fintype.ofFinite _
  have hΔ : Fintype.card ↥(nbrs w) = 5 := by
    rw [← Nat.card_eq_fintype_card]; exact hA.card_nbrs w
  obtain ⟨z', hz'γ, hz'Q, hzz'Q⟩ := exists_third_v F hw hγ hzγ hzQ
  have hz's : z' ∈ stab w := hA.Qv_le_stab_of_mem_nbrs
    ((show (graph _ _ _).Adj w γ from hγ).symm) hz'γ
  let z'q : ↥(stab w) := ⟨z', hz's⟩
  obtain ⟨x, hx, hxγ, -⟩ := exists_nbr_ne_two F hγ hγ
  obtain ⟨A, B, hAe, hBe, h1, h2'', h3, h4', h5, h6', h7, h8, h9, h10, h11, h12⟩ :=
    four_points F hw hγ hx hxγ (a := z') (b := z) hz'γ hzγ hz'Q hzQ hzz'Q
      (by rw [hz2]; exact (Qv w).one_mem)
  have hgz : gm zq = B := Subtype.ext hBe.symm
  have hgz' : gm z'q = A := Subtype.ext hAe.symm
  let p0 : ↥(nbrs w) := ⟨γ, hγ⟩
  let p1 : ↥(nbrs w) := ⟨x, hx⟩
  let p2 : ↥(nbrs w) := ⟨B • x, h11⟩
  let p3 : ↥(nbrs w) := ⟨A • x, h10⟩
  let p4 : ↥(nbrs w) := ⟨(B * A) • x, h12⟩
  have hz1p : zq • p1 = p2 := Subtype.ext (by rw [hsmulΩ, hgz])
  have hz1p' : z'q • p1 = p3 := Subtype.ext (by rw [hsmulΩ, hgz'])
  have hz3p : zq • p3 = p4 := Subtype.ext (by
    rw [hsmulΩ, hgz]; exact (mul_smul B A x).symm)
  have hlist : ([p0, p1, p2, p3, p4] : List ↥(nbrs w)).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
      and_true]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, not_false⟩ <;>
      intro h <;> have h' := congrArg Subtype.val h <;> simp only [p0, p1, p2, p3, p4] at h'
    · exact hxγ h'.symm
    · exact h8 h'.symm
    · exact h7 h'.symm
    · exact h9 h'.symm
    · exact h2'' h'.symm
    · exact h1 h'.symm
    · exact h3 h'.symm
    · exact h4' h'.symm
    · exact h6' h'
    · exact h5 h'
  have huniv : ∀ y : ↥(nbrs w), y ∈ ([p0, p1, p2, p3, p4] : List ↥(nbrs w)) := by
    intro y
    by_contra hy
    have hnd : (y :: ([p0, p1, p2, p3, p4] : List ↥(nbrs w))).Nodup :=
      List.nodup_cons.mpr ⟨hy, hlist⟩
    have := hnd.length_le_card
    simp [hΔ] at this
  have hzz : φ (zq * zq) = 1 := (hφk' _).mpr (by
    show z * z ∈ Qv w; rw [hz2]; exact (Qv w).one_mem)
  have hzz' : φ (z'q * z'q) = 1 := (hφk' _).mpr
    (sq_mem_Qv_of_mem_nbrs F hw hγ hz'γ)
  have hcomm : φ (zq * z'q) = φ (z'q * zq) := by
    have hc := (hφk' (zq * z'q * zq⁻¹ * z'q⁻¹)).mpr (comm_mem_Qv F hw hγ hzγ hz'γ)
    simp only [map_mul, map_inv] at hc
    have h0 : ⁅φ zq, φ z'q⁆ = 1 := by rw [commutatorElement_def]; exact hc
    have := commutatorElement_eq_one_iff_mul_comm.mp h0
    simpa only [map_mul] using this
  have hZ' : ∀ u ∈ (Zv γ).subgroupOf (Vn w), ∀ b : ↥(stab w), b • p0 = p0 →
      ρ b u * u⁻¹ ∈ qcomm ρ φ.ker ⊤ := by
    intro u hu b hb
    have hbγ : (b : G) ∈ stab γ := by
      have : gm b • γ = γ := by
        have := congrArg Subtype.val hb
        simpa [hsmulΩ, p0] using this
      exact mem_stab_of_smul_eq (g := gm b) this
    have hv : (u : G) ∈ Zv γ := Subgroup.mem_subgroupOf.mp hu
    have h1 := edge_trivial_mod F hZ hw hγ (g := (b : G)) (Subgroup.mem_inf.mpr ⟨hbγ, b.2⟩) hv
    have h2' := hQ2 h1
    obtain ⟨y, hy, hye⟩ := h2'
    have : y = ρ b u * u⁻¹ := Subtype.ext (by
      rw [Subgroup.coe_mul, hρ, Subgroup.coe_inv]; exact hye)
    rw [← this]; exact hy
  have h7 := relIndex_Cfix_le_two (ρ := ρ) h2 φ hφs hnil hφ1 hφ2 hbound' hnt p0 p1 p2 p3 p4 hlist
    huniv hz1p hz1p' hz3p hzz hzz' hcomm ((Zv γ).subgroupOf (Vn w)) hZ'
  have hZle : Zv γ ≤ Vn w := hA.Zv_le_Vn hγ
  let C' : Subgroup G := (Cfix ρ).map (Vn w).subtype
  have hC'rel : (Zv γ ⊓ C').relIndex (Zv γ) ≤ 2 := by
    have e1 := Subgroup.relIndex_map_map_of_injective (f := (Vn w).subtype) (Cfix ρ)
      ((Zv γ).subgroupOf (Vn w)) (Subgroup.subtype_injective _)
    rw [Subgroup.map_subgroupOf_eq_of_le hZle] at e1
    rw [inf_comm, Subgroup.inf_relIndex_right, e1]
    exact h7
  let Pg : Subgroup G := (oddNC ↥(stab w)).map (stab w).subtype
  have hPcent : ∀ s ∈ Pg, ∀ c ∈ C', s * c = c * s := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨c0, hc0, rfl⟩
    have h1 := oddNC_fix (ρ := ρ) hg c0 hc0
    have h2' := congrArg (fun v : ↥(Vn w) => (v : G)) h1
    simp only [hρ] at h2'
    show (g : G) * (c0 : G) = (c0 : G) * (g : G)
    calc (g : G) * (c0 : G) = ((g : G) * (c0 : G) * (g : G)⁻¹) * (g : G) := by group
      _ = (c0 : G) * (g : G) := by rw [h2']
  have hPle : Pg ≤ stab w := by
    rintro _ ⟨g, -, rfl⟩; exact g.2
  have hPnorm : ∀ p ∈ Pg, ∀ t ∈ stab w, t * p * t⁻¹ ∈ Pg := by
    rintro _ ⟨g, hg, rfl⟩ t ht
    have : (oddNC ↥(stab w)).Normal := Subgroup.normalClosure_normal
    exact ⟨⟨t, ht⟩ * g * ⟨t, ht⟩⁻¹, Subgroup.Normal.conj_mem inferInstance g hg ⟨t, ht⟩, rfl⟩
  have hPtrans : ∀ x' ∈ nbrs w, ∃ p ∈ Pg, ∃ hp : p ∈ P1 L1 L2 S ⊔ P2 L1 L2 S,
      (⟨p, hp⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) • γ = x' := by
    intro x' hx'
    obtain ⟨q, hq, hqγ⟩ := exists_stab_smul_nbr F hw hγ hx'
    let g0 : ↥(stab w) := ⟨q, hq⟩
    have hmem : φ g0 ∈ (oddNC ↥(stab w)).map φ := by
      rw [oddNC_map_top φ hφs]; exact Subgroup.mem_top _
    obtain ⟨p, hpo, hpg⟩ := hmem
    have hq0 : (p⁻¹ * g0 : ↥(stab w)) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpg, inv_mul_cancel]
    have hq0Q : (((p⁻¹ * g0 : ↥(stab w))) : G) ∈ Qv w := by
      rw [hφk, Subgroup.mem_subgroupOf] at hq0; exact hq0
    have hq0γ : (((p⁻¹ * g0 : ↥(stab w))) : G)⁻¹ ∈ stab γ :=
      Subgroup.inv_mem _ (hA.Qv_le_stab_of_mem_nbrs hγ hq0Q)
    refine ⟨(p : G), ⟨p, hpo, rfl⟩, stab_le _ p.2, ?_⟩
    have hpe : (⟨(p : G), stab_le _ p.2⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) =
        gm g0 * ⟨(((p⁻¹ * g0 : ↥(stab w))) : G)⁻¹, stab_le _ (by simpa using hq0γ)⟩ := by
      apply Subtype.ext
      simp [gm, g0]
    rw [hpe, mul_smul]
    have : (⟨(((p⁻¹ * g0 : ↥(stab w))) : G)⁻¹, stab_le _ (by simpa using hq0γ)⟩ :
        ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) • γ = γ := smul_eq_of_mem_stab (g := _) hq0γ
    rw [this]
    exact hqγ
  exact NT_of_relIndex F hw hγ hγf hZFγ C' Pg hC'rel hPcent hPle hPnorm hPtrans

end Core

section Final

theorem relIndex_le_two_of {H K : Subgroup G}
    (h : ∀ a ∈ K, ∀ b ∈ K, a ∈ H ∨ b ∈ H ∨ b * a ∈ H) : (H ⊓ K).relIndex K ≤ 2 := by
  have hdvd : (H ⊓ K).relIndex K ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff']
    by_cases hex : ∃ a ∈ K, a ∉ H
    · obtain ⟨a, haK, haH⟩ := hex
      refine ⟨a, haK, fun b hb => ?_⟩
      rcases h b hb a haK with h1 | h1 | h1
      · exact Or.inr (Subgroup.mem_inf.mpr ⟨h1, hb⟩)
      · exact absurd h1 haH
      · exact Or.inl (Subgroup.mem_inf.mpr ⟨h1, K.mul_mem haK hb⟩)
    · push Not at hex
      refine ⟨1, K.one_mem, fun b hb => Or.inr (Subgroup.mem_inf.mpr ⟨hex b hb, hb⟩)⟩
  exact Nat.le_of_dvd two_pos hdvd

variable (F : Frame L1 L2 S D X) (hb3 : 3 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S))
  (hZ : ∀ μ : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype μ = true → Zv μ ≤ centerOf (stab μ))
include F hb3

theorem double_comm_one {μ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} {v a b : G} (hv : v ∈ stab μ)
    (ha : a ∈ Vn μ) (hb : b ∈ Vn μ) : ⁅⁅v, a⁆, b⁆ = 1 := by
  have hA := Amal.of_frame F
  have hMab := hA.isElemAbelian_Vn hb3 μ
  have h1 : v * a * v⁻¹ ∈ Vn μ :=
    (Subgroup.mem_normalizer_iff.mp (Amal.stab_le_normalizer_Vn' μ hv) a).mp ha
  have h2 : ⁅v, a⁆ ∈ Vn μ := by
    rw [commutatorElement_def]; exact (Vn μ).mul_mem h1 ((Vn μ).inv_mem ha)
  exact commutatorElement_eq_one_iff_commute.mpr (isElemAbelian_comm hMab h2 hb)

include hZ

theorem klein_E {w β v2 γ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hw : vtype w = true)
    (hγw : γ ∈ nbrs w) (hv2β : v2 ∈ nbrs β) (hN : Vn β ≤ Qv γ) (hM : Vn w ≤ Qv v2) :
    ∀ a ∈ Vn β, ∀ b ∈ Vn β, a ∈ Qv w ∨ b ∈ Qv w ∨ b * a ∈ Qv w := by
  have hA := Amal.of_frame F
  intro a ha b hb
  by_contra h
  push Not at h
  obtain ⟨h1, h2, h3⟩ := h
  refine klein_false F hb3 hZ hw hγw (hN ha) (hN hb) h1 h2 h3 (fun v hv => ?_)
  have hvs : v ∈ stab β := hA.Qv_le_stab_of_mem_nbrs
    ((show (graph _ _ _).Adj β v2 from hv2β).symm) (hM hv)
  exact double_comm_one F hb3 hvs ha hb

theorem klein_F {w β v2 γ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hβ : vtype β = true)
    (hv2β : v2 ∈ nbrs β) (hγw : γ ∈ nbrs w) (hN : Vn β ≤ Qv γ) (hM : Vn w ≤ Qv v2) :
    ∀ a ∈ Vn w, ∀ b ∈ Vn w, a ∈ Qv β ∨ b ∈ Qv β ∨ b * a ∈ Qv β := by
  have hA := Amal.of_frame F
  intro a ha b hb
  by_contra h
  push Not at h
  obtain ⟨h1, h2, h3⟩ := h
  refine klein_false F hb3 hZ hβ hv2β (hM ha) (hM hb) h1 h2 h3 (fun v hv => ?_)
  have hvs : v ∈ stab w := hA.Qv_le_stab_of_mem_nbrs
    ((show (graph _ _ _).Adj w γ from hγw).symm) (hN hv)
  exact double_comm_one F hb3 hvs ha hb

theorem t2_config_false
    (hZFD : ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype δ = false → ZFaithful δ)
    {α β v2 γ w : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hα : vtype α = false) (hβ : vtype β = true)
    (hw : vtype w = true) (hγf : vtype γ = false) (hαβ : α ∈ nbrs β) (hv2β : v2 ∈ nbrs β)
    (hγw : γ ∈ nbrs w) (hN : Vn β ≤ Qv γ) (hM : Vn w ≤ Qv v2) (hnot : ¬ Zv α ≤ Qv w) :
    False := by
  have hA := Amal.of_frame F
  have hMab := hA.isElemAbelian_Vn hb3 w
  obtain ⟨z, hzZ, hzQ⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hZα : Zv α ≤ Vn β := hA.Zv_le_Vn hαβ
  have hz2 : z * z = 1 := by rw [← pow_two]; exact (hA.isElemAbelian_Zv α).2 z hzZ
  have hzγ : z ∈ Qv γ := hN (hZα hzZ)
  obtain ⟨h4, hNT⟩ := core_geo F hb3 hZ hw hγw hγf (hZFD γ hγf) hzγ hzQ hz2
  have hβs : Qv β ≤ stab α := hA.Qv_le_stab_of_mem_nbrs hαβ
  have hQcent : ∀ y ∈ Qv α, z * y = y * z := fun y hy =>
    Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv F α hy) z hzZ
  have hF2 : (Qv β ⊓ Vn w).relIndex (Vn w) ≤ 2 :=
    relIndex_le_two_of (klein_F F hb3 hZ hβ hv2β hγw hN hM)
  have hA2 : IsElemAbelian 2 (Vn w ⊓ Qv β) :=
    ⟨⟨⟨fun a b => Subtype.ext (isElemAbelian_comm hMab a.2.1 b.2.1)⟩⟩, fun a ha => hMab.2 a ha.1⟩
  have hX : ((Vn w ⊓ Qv β) ⊓ Qv α).relIndex (Vn w ⊓ Qv β) ≤ 2 :=
    relIndex_inf_Qv_le_two F hα (inf_le_right.trans hβs) hA2
  have hbound : (Vn w ⊓ Subgroup.centralizer ({z} : Set G)).relIndex (Vn w) ≤ 4 := by
    have hsub : (Vn w ⊓ Qv β) ⊓ Qv α ≤ Vn w ⊓ Subgroup.centralizer ({z} : Set G) := by
      refine le_inf (inf_le_left.trans inf_le_left) fun y hy => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]; exact hQcent y (Subgroup.mem_inf.mp hy).2
    have h1 := Subgroup.relIndex_le_of_le_left (L := Vn w) hsub (relIndex_ne_zero_G _ _)
    have h2 := Subgroup.relIndex_mul_relIndex ((Vn w ⊓ Qv β) ⊓ Qv α) (Vn w ⊓ Qv β) (Vn w)
      inf_le_left inf_le_left
    have h3 : (Vn w ⊓ Qv β).relIndex (Vn w) ≤ 2 := by
      rw [inf_comm]; exact hF2
    calc (Vn w ⊓ Subgroup.centralizer ({z} : Set G)).relIndex (Vn w)
        ≤ ((Vn w ⊓ Qv β) ⊓ Qv α).relIndex (Vn w) := h1
      _ = ((Vn w ⊓ Qv β) ⊓ Qv α).relIndex (Vn w ⊓ Qv β) * (Vn w ⊓ Qv β).relIndex (Vn w) := h2.symm
      _ ≤ 2 * 2 := Nat.mul_le_mul hX h3
  have hNT' := hNT hbound
  have hK : ∀ k ∈ Vn β ⊓ Qv w, ∀ m ∈ Vn w, k * m = m * k := by
    intro k hk m hm
    have hkγ : k ∈ Qv w ⊓ Qv γ := Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hk).2,
      hN (Subgroup.mem_inf.mp hk).1⟩
    have hle : Vn w ≤ Subgroup.centralizer ({k} : Set G) := by
      refine iSup₂_le fun x hx y hy => ?_
      have hkx : k ∈ Qv x := by
        have : k ∈ Qv w ⊓ Qv x := by rw [hNT' x hx]; exact hkγ
        exact (Subgroup.mem_inf.mp this).2
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv F x hkx) y hy).symm
    exact Subgroup.mem_centralizer_iff.mp (hle hm) k (Set.mem_singleton k)
  have hE : (Qv w ⊓ Zv α).relIndex (Zv α) ≤ 2 :=
    relIndex_le_two_of fun a ha b hb => klein_E F hb3 hZ hw hγw hv2β hN hM a (hZα ha) b (hZα hb)
  have hM2 : ∀ w' ∈ Vn w ⊓ Qv β, w' ∈ Qv α := by
    intro w' hw'
    by_contra hn
    have hw's : w' ∈ stab α := hβs (Subgroup.mem_inf.mp hw').2
    have hw'2 : w' ^ 2 = 1 := hMab.2 w' (Subgroup.mem_inf.mp hw').1
    have hsub : Qv w ⊓ Zv α ≤ Zv α ⊓ Subgroup.centralizer ({w'} : Set G) := by
      refine le_inf inf_le_right fun c hc => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hK c (Subgroup.mem_inf.mpr ⟨hZα (Subgroup.mem_inf.mp hc).2, (Subgroup.mem_inf.mp hc).1⟩)
        w' (Subgroup.mem_inf.mp hw').1).symm
    have hidx2 := (Subgroup.relIndex_le_of_le_left (L := Zv α) hsub (relIndex_ne_zero_G _ _)).trans hE
    exact no_transvection_Zv F hα (hZFD α hα) hw's hn (by rw [hw'2]; exact (Qv α).one_mem)
      (k := 1) (by rw [pow_one, pow_two]; simpa [sq] using hw'2) hidx2
  have hsub2 : Vn w ⊓ Qv β ≤ Vn w ⊓ Subgroup.centralizer ({z} : Set G) := by
    refine le_inf inf_le_left fun y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]; exact hQcent y (hM2 y hy)
  have h5 := Subgroup.relIndex_le_of_le_left (L := Vn w) hsub2 (relIndex_ne_zero_G _ _)
  have h3 : (Vn w ⊓ Qv β).relIndex (Vn w) ≤ 2 := by
    rw [inf_comm]; exact hF2
  omega

end Final

end CFSG.Quasithin.Kleidman.F204
