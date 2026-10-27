module

public import CFSG.RankThree.GF2n.Tim81.Sec5.HBarAut
public import CFSG.RankThree.GF2n.Tim81.Sec5.SigmaData
public import CFSG.RankThree.GF2n.Tim81.Sec2.NatSumFixed

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.RankThree.GF2n.Tim81.Sec4 CFSG.GroupTheory CFSG.QuasithinUnique.Setup.X7
open CFSG.LocalAnalysis.EvenBN.Common
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {M V : Subgroup G}

private theorem xOf_le_centralizer_kOf {H : Subgroup G} {c : G}
    (hS : Sec45Shape M V H c) :
    kOf V H ≤ Subgroup.centralizer (Tim79a.xOf V H : Set G) := by
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  refine Subgroup.le_centralizer_iff.mpr ?_
  rw [← hw.center_K]
  exact inf_le_right

private theorem exists_mem_conj_eq_of_map_range_eq_xOf {H : Subgroup G} {H₁ : Subgroup G} {y : G}
    (h : RootHyp M V) (hyH : y ∈ H)
    (χ : ↥H₁ →* ↥(Tim79a.xOf V H))
    (htop : χ.range.map (Tim79a.xOf V H).subtype = Tim79a.xOf V H) :
    ∃ (w : ↥(conjSubgroup y V)) (a : ↥H₁), (w : G) ≠ 1 ∧
      (Tim79a.xOf V H).subtype (χ a) = (w : G) := by
  have hVne : conjSubgroup y V ≠ ⊥ := fun hbot =>
    h.toHyp.ne_bot (conjSubgroup_eq_bot_iff.mp hbot)
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
  have hw1' : (w : G) ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
  have hwW : (w : G) ∈ Tim79a.xOf V H := conjSubgroup_le_xOf_of_mem hyH w.2
  have hwW' : (w : G) ∈ χ.range.map (Tim79a.xOf V H).subtype := htop.symm ▸ hwW
  obtain ⟨u, hu, huw⟩ := Subgroup.mem_map.mp hwW'
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hu
  exact ⟨w, a, hw1', by rw [← huw, ha]⟩


private theorem Sec45Shape.exists_mem_conjSubgroup_Pc_not_mem_kOf {H : Subgroup G} {h₀ : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀) :
    ∃ y ∈ conjSubgroup h₀ (Pc M V), y ∉ kOf V H := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  obtain ⟨-, -, a, b, ha, hb, hne'⟩ :=
    RootHyp.imgK_map_sl2 h hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ
  have hcard : Nat.card (imgK V H (conjSubgroup h₀ (Pc M V))) = 2 ^ (2 * l) := by
    rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hb, card_conjSubgroup,
      card_utri, ← hl, Nat.card_eq_fintype_card]
  have hne : imgK V H (conjSubgroup h₀ (Pc M V)) ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (imgK V H (conjSubgroup h₀ (Pc M V))) = 1 := by rw [hbot]; simp
    rw [hcard] at h1
    have hl1 : 1 ≤ l := hw.one_le
    have h4 : 4 ≤ 2 ^ (2 * l) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * l) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨y, hyS, hyq⟩ := (mem_imgK_iff).mp z.2
  refine ⟨y, hyS, ?_⟩
  intro hyK
  exact hz (Subtype.ext (by rw [← hyq]; exact (piK_eq_one_iff y).mpr hyK))

private theorem mem_commSub_zpowers_of_repSec_apply {H : Subgroup G} {c x y : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H c) (hcH : c ∈ H) (hyH : y ∈ H)
    (hs : CFSG.Timmesfeld.Bridge.QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal]
    [Module (ZMod 2) (SecMod hs)]
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F))
    (hσ : Sec2.IsNatSumModule (repSec hs hs.comm SL(2, F) ψ))
    {t : SL(2, F)} (ht : t = ψ (piK V H ⟨y, hyH⟩)) (ht1 : t ≠ 1)
    (htA : t ∈ (imgK V H (conjSubgroup c (Pc M V))).map ψ.toMonoidHom)
    (hxy : ⁅y, x⁆ ∈ kOf V H) (hy2V : y * y ∈ conjSubgroup c V)
    (hxcent : x ∈ Subgroup.centralizer (conjSubgroup c V : Set G)) :
    SecMod.mk hs ⟨⁅y, x⁆, hxy⟩ ∈
      commSub (repSec hs hs.comm SL(2, F) ψ) (Subgroup.zpowers t) := by
  let yH : ↥H := ⟨y, hyH⟩
  let n0 : ↥(kOf V H) := ⟨⁅y, x⁆, hxy⟩
  let d : SecMod hs := SecMod.mk hs n0
  have hσd : repSec hs hs.comm SL(2, F) ψ t d =
      SecMod.mk hs ⟨y * ⁅y, x⁆ * y⁻¹, hs.conj yH hyH n0 hxy⟩ := by
    rw [ht, show d = SecMod.mk hs n0 from rfl]
    exact repSec_apply_piK_mk hs hs.comm SL(2, F) ψ yH n0
  have hcomm_y2 : ⁅y * y, x⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp hxcent (y * y) hy2V
  have h1 : y * ⁅y, x⁆ * y⁻¹ * ⁅y, x⁆ = 1 := by
    rw [← commutatorElement_mul_left_eq_conj_mul]
    exact hcomm_y2
  have h1K : y * ⁅y, x⁆ * y⁻¹ * ⁅y, x⁆ ∈ kOf V H := h1 ▸ (kOf V H).one_mem
  have h1W : y * ⁅y, x⁆ * y⁻¹ * ⁅y, x⁆ ∈ Tim79a.xOf V H := h1 ▸ (Tim79a.xOf V H).one_mem
  have h2 : repSec hs hs.comm SL(2, F) ψ t d + d = 0 := by
    rw [hσd, show d = SecMod.mk hs n0 from rfl, ← SecMod.mk_mul hs, SecMod.mk_eq_zero_iff hs,
      show ((⟨y * ⁅y, x⁆ * y⁻¹, hs.conj yH hyH n0 hxy⟩ : ↥(kOf V H)) * n0 : ↥(kOf V H)) =
        ⟨y * ⁅y, x⁆ * y⁻¹ * ⁅y, x⁆, h1K⟩ from Subtype.ext rfl]
    simpa using h1W
  have h3 : repSec hs hs.comm SL(2, F) ψ t d = d := by
    have hdd : d + d = 0 := by
      have h2' : (2 : ZMod 2) • d = 0 := by
        rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
      rwa [two_smul] at h2'
    calc repSec hs hs.comm SL(2, F) ψ t d
        = repSec hs hs.comm SL(2, F) ψ t d + 0 := (add_zero _).symm
      _ = repSec hs hs.comm SL(2, F) ψ t d + (d + d) := by rw [hdd]
      _ = (repSec hs hs.comm SL(2, F) ψ t d + d) + d := by abel
      _ = 0 + d := by rw [h2]
      _ = d := zero_add d
  have hdfix : d ∈ fixedSub (repSec hs hs.comm SL(2, F) ψ) (Subgroup.zpowers t) := by
    rw [fixedSub_zpowers, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, h3,
      sub_self]
  have hpair := hS.map_imgK_conj_sylow h ψ hcH
  have hfin := Sec2.IsNatSumModule.fixedSub_zpowers_eq hσ hpair.1 hpair.2 htA ht1
  have hdmem : d ∈ commSub (repSec hs hs.comm SL(2, F) ψ) (Subgroup.zpowers t) := by
    rw [hfin.2, ← hfin.1]
    exact hdfix
  exact hdmem

private theorem exists_mem_kOf_commutator_congr_of_mem_commSub {H : Subgroup G} {x y : G}
    (hs : CFSG.Timmesfeld.Bridge.QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal]
    [Module (ZMod 2) (SecMod hs)]
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F)) (hyH : y ∈ H)
    {t : SL(2, F)} (ht : t = ψ (piK V H ⟨y, hyH⟩)) (ht2 : t * t = 1)
    (hxy : ⁅y, x⁆ ∈ kOf V H)
    (hdmem : SecMod.mk hs ⟨⁅y, x⁆, hxy⟩ ∈
      commSub (repSec hs hs.comm SL(2, F) ψ) (Subgroup.zpowers t)) :
    ∃ a ∈ kOf V H, ⁅y, a⁆⁻¹ * ⁅y, x⁆ ∈ Tim79a.xOf V H := by
  let yH : ↥H := ⟨y, hyH⟩
  let n0 : ↥(kOf V H) := ⟨⁅y, x⁆, hxy⟩
  rw [Sec2.commSub_zpowers_eq_range _ ht2] at hdmem
  obtain ⟨v, hv⟩ := hdmem
  obtain ⟨a₀, rfl⟩ := SecMod.mk_surjective hs v
  have hv' : SecMod.mk hs ⟨y * (a₀ : G) * y⁻¹, hs.conj yH hyH a₀ a₀.2⟩ -
      SecMod.mk hs a₀ = SecMod.mk hs ⟨⁅y, x⁆, hxy⟩ := by
    simpa only [ht, yH, LinearMap.sub_apply, Module.End.one_apply,
      repSec_apply_piK_mk hs hs.comm SL(2, F) ψ yH a₀] using hv
  have hbmem : y * (a₀ : G) * y⁻¹ * (a₀ : G)⁻¹ ∈ kOf V H :=
    (kOf V H).mul_mem (hs.conj yH hyH a₀ a₀.2) ((kOf V H).inv_mem a₀.2)
  let b : ↥(kOf V H) := ⟨⁅y, (a₀ : G)⁆, hbmem⟩
  have hb : b = ⟨y * (a₀ : G) * y⁻¹, hs.conj yH hyH a₀ a₀.2⟩ * a₀⁻¹ := Subtype.ext rfl
  have hmkb : SecMod.mk hs b = SecMod.mk hs ⟨⁅y, x⁆, hxy⟩ := by
    rw [hb, SecMod.mk_mul, SecMod.mk_inv]
    simpa [sub_eq_add_neg] using hv'
  refine ⟨(a₀ : G), a₀.2, ?_⟩
  have hzero : SecMod.mk hs (b⁻¹ * n0) = 0 := by
    rw [SecMod.mk_mul, SecMod.mk_inv, hmkb, neg_add_cancel]
  exact (SecMod.mk_eq_zero_iff hs _).mp hzero

private theorem Sec45Shape.exists_mem_kOf_commutator_congr {H : Subgroup G} {c x y : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H c) (hcH : c ∈ H)
    (hy : y ∈ conjSubgroup c (Pc M V)) (hyK : y ∉ kOf V H)
    (hxy : ⁅y, x⁆ ∈ kOf V H)
    (hxcent : x ∈ Subgroup.centralizer (conjSubgroup c V : Set G)) :
    ∃ a ∈ kOf V H, ⁅y, a⁆⁻¹ * ⁅y, x⁆ ∈ Tim79a.xOf V H := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hK := hS.quotModHyp h
  haveI hKnorm : ((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal := hK.normal
  haveI hmod : Module (ZMod 2) (SecMod hK) := SecMod.module hK hw.sq_mem
  have hσ : Sec2.IsNatSumModule (repSec hK hK.comm SL(2, F) ψ) :=
    hw.natSum hK (inferInstance : Module (ZMod 2) (SecMod hK))
  have hyH : y ∈ H := conjSubgroup_le_of_le_of_mem hS.Pc_le hcH hy
  let yH : ↥H := ⟨y, hyH⟩
  let t : SL(2, F) := ψ (piK V H yH)
  have hy2V : y * y ∈ conjSubgroup c V := h.sq_mem_conjSubgroup_V_of_mem_conjSubgroup_Pc hy
  have hy2K : y * y ∈ kOf V H :=
    RootHyp.conjSubgroup_le_kOf_of_mem h hS.Pc_le hS.le_pCore hcH hy2V
  have ht2 : t * t = 1 := by
    have h2 : piK V H yH * piK V H yH = 1 := by
      rw [← map_mul]
      exact (piK_eq_one_iff (yH * yH)).mpr (by simpa using hy2K)
    rw [show t * t = ψ (piK V H yH) * ψ (piK V H yH) from rfl, ← map_mul, h2, map_one]
  have ht1 : t ≠ 1 := by
    intro h1
    refine hyK ((piK_eq_one_iff yH).mp ?_)
    have h2 : t = ψ (piK V H yH) := rfl
    rw [h2] at h1
    exact ψ.injective (by simpa using h1)
  have htA : t ∈ (imgK V H (conjSubgroup c (Pc M V))).map ψ.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨piK V H yH, (mem_imgK_iff).mpr ⟨yH, hy, rfl⟩, rfl⟩
  have hpair := hS.map_imgK_conj_sylow h ψ hcH
  let n0 : ↥(kOf V H) := ⟨⁅y, x⁆, hxy⟩
  let d : SecMod hK := SecMod.mk hK n0
  have hσd : repSec hK hK.comm SL(2, F) ψ t d =
      SecMod.mk hK ⟨y * ⁅y, x⁆ * y⁻¹, hK.conj yH hyH n0 hxy⟩ :=
    repSec_apply_piK_mk hK hK.comm SL(2, F) ψ yH n0
  have hdmem : d ∈ commSub (repSec hK hK.comm SL(2, F) ψ) (Subgroup.zpowers t) :=
    mem_commSub_zpowers_of_repSec_apply (hs := hK) h hS hcH hyH ψ hσ rfl ht1 htA
      hxy hy2V hxcent
  exact exists_mem_kOf_commutator_congr_of_mem_commSub (hs := hK) ψ hyH rfl ht2 hxy hdmem

private theorem Sec45Shape.exists_mem_inf_Pc_mul_inv_mem_xOf {H : Subgroup G} {c a : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H c) (ha : a ∈ kOf V H) :
    ∃ a₁ ∈ Pc M V ⊓ kOf V H, ∃ a₂ ∈ conjSubgroup c (Pc M V) ⊓ kOf V H,
      (a₁ * a₂)⁻¹ * a ∈ Tim79a.xOf V H := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hK := hS.quotModHyp h
  haveI hKnorm : ((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal := hK.normal
  haveI hmod : Module (ZMod 2) (SecMod hK) := SecMod.module hK hw.sq_mem
  have hsplit : subSec hK (Pc M V ⊓ kOf V H) ⊔
      subSec hK (conjSubgroup c (Pc M V) ⊓ kOf V H) = ⊤ := by
    rw [← subSec_sup hK (inf_le_right : Pc M V ⊓ kOf V H ≤ kOf V H)
      (inf_le_right : conjSubgroup c (Pc M V) ⊓ kOf V H ≤ kOf V H), ← hS.kFact, subSec_self]
  have hmem : (SecMod.mk hK ⟨a, ha⟩ : SecMod hK) ∈
      subSec hK (Pc M V ⊓ kOf V H) ⊔ subSec hK (conjSubgroup c (Pc M V) ⊓ kOf V H) := by
    rw [hsplit]
    exact Submodule.mem_top
  obtain ⟨u₁, hu₁, u₂, hu₂, hsum⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨n₁, hn₁⟩ := (mem_subSec_iff hK).mp hu₁
  obtain ⟨n₂, hn₂⟩ := (mem_subSec_iff hK).mp hu₂
  set a₁ : G := (n₁ : G) with ha₁def
  set a₂ : G := (n₂ : G) with ha₂def
  have ha₁ : a₁ ∈ Pc M V ⊓ kOf V H := n₁.2.1
  have ha₂ : a₂ ∈ conjSubgroup c (Pc M V) ⊓ kOf V H := n₂.2.1
  have ha₁K : a₁ ∈ kOf V H := ha₁.2
  have ha₂K : a₂ ∈ kOf V H := ha₂.2
  have hmem₁ : SecMod.mk hK ⟨a₁, ha₁K⟩ = u₁ := by
    rw [← hn₁, show Subgroup.inclusion inf_le_right n₁ = ⟨a₁, ha₁K⟩ from Subtype.ext rfl]
  have hmem₂ : SecMod.mk hK ⟨a₂, ha₂K⟩ = u₂ := by
    rw [← hn₂, show Subgroup.inclusion inf_le_right n₂ = ⟨a₂, ha₂K⟩ from Subtype.ext rfl]
  have hmk_eq : SecMod.mk hK ⟨a₁ * a₂, (kOf V H).mul_mem ha₁K ha₂K⟩ =
      SecMod.mk hK ⟨a, ha⟩ := by
    rw [show (⟨a₁ * a₂, (kOf V H).mul_mem ha₁K ha₂K⟩ : ↥(kOf V H)) =
      ⟨a₁, ha₁K⟩ * ⟨a₂, ha₂K⟩ from Subtype.ext rfl, SecMod.mk_mul, hmem₁, hmem₂]
    exact hsum
  have hWa : (a₁ * a₂)⁻¹ * a ∈ Tim79a.xOf V H :=
    (CFSG.Timmesfeld.Bridge.QuotMod.mk_eq_mk_iff (N := kOf V H)
      (N₀ := Tim79a.xOf V H) _ _).mp hmk_eq
  exact ⟨a₁, ha₁, a₂, ha₂, hWa⟩

private theorem Sec45Shape.commutatorElement_congr_of_mul_mem_xOf {H : Subgroup G}
    {c y a a₁ a₂ : G} (h : RootHyp M V) (hS : Sec45Shape M V H c) (hcH : c ∈ H)
    (hyH : y ∈ H) (hy : y ∈ conjSubgroup c (Pc M V))
    (ha₁ : a₁ ∈ Pc M V ⊓ kOf V H) (ha₂ : a₂ ∈ conjSubgroup c (Pc M V) ⊓ kOf V H)
    (hWa : (a₁ * a₂)⁻¹ * a ∈ Tim79a.xOf V H) :
    ⁅y, a₁⁆⁻¹ * ⁅y, a⁆ ∈ Tim79a.xOf V H := by
  classical
  have ha₁K : a₁ ∈ kOf V H := ha₁.2
  have ha₂K : a₂ ∈ kOf V H := ha₂.2
  have hya₂W : ⁅y, a₂⁆ ∈ Tim79a.xOf V H := by
    have hy' : c⁻¹ * y * c ∈ Pc M V := mem_conjSubgroup.mp hy
    have ha₂' : c⁻¹ * a₂ * c ∈ Pc M V := mem_conjSubgroup.mp ha₂.1
    have hcc := Subgroup.commutator_mem_commutator hy' ha₂'
    rw [hS.commutator_Pc h] at hcc
    have hconj : ⁅y, a₂⁆ = c * ⁅c⁻¹ * y * c, c⁻¹ * a₂ * c⁆ * c⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [hconj]
    refine conjSubgroup_le_xOf_of_mem hcH (mem_conjSubgroup.mpr ?_)
    rw [show c⁻¹ * (c * ⁅c⁻¹ * y * c, c⁻¹ * a₂ * c⁆ * c⁻¹) * c =
      ⁅c⁻¹ * y * c, c⁻¹ * a₂ * c⁆ by group]
    exact hcc
  have hyNW : y ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) :=
    Tim79a.H_le_normalizer_xOf V H hyH
  have hA : ⁅y, a₁ * a₂⁆ = ⁅y, a₁⁆ * (a₁ * ⁅y, a₂⁆ * a₁⁻¹) := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    group
  have hAW : a₁ * ⁅y, a₂⁆ * a₁⁻¹ ∈ Tim79a.xOf V H :=
    ((Subgroup.mem_normalizer_iff.mp
      (Tim79a.H_le_normalizer_xOf V H (kOf_le V H ha₁K))) _).mp hya₂W
  have hcongA : ⁅y, a₁⁆⁻¹ * ⁅y, a₁ * a₂⁆ ∈ Tim79a.xOf V H := by
    rw [hA]
    rw [show ⁅y, a₁⁆⁻¹ * (⁅y, a₁⁆ * (a₁ * ⁅y, a₂⁆ * a₁⁻¹)) =
      a₁ * ⁅y, a₂⁆ * a₁⁻¹ by group]
    exact hAW
  have hw : (a₁ * a₂)⁻¹ * a ∈ Tim79a.xOf V H := hWa
  have hB : ⁅y, a⁆ = ⁅y, a₁ * a₂⁆ *
      (a₁ * a₂ * ⁅y, (a₁ * a₂)⁻¹ * a⁆ * (a₁ * a₂)⁻¹) := by
    conv_lhs => rw [show a = a₁ * a₂ * ((a₁ * a₂)⁻¹ * a) by group]
    rw [commutatorElement_mul_right_eq_mul_conj]
    group
  have hyW : ∀ b ∈ Tim79a.xOf V H, ⁅y, b⁆ ∈ Tim79a.xOf V H := fun b hb => by
    have h1 : y * b * y⁻¹ ∈ Tim79a.xOf V H := ((Subgroup.mem_normalizer_iff.mp hyNW) b).mp hb
    have h2 : ⁅y, b⁆ = (y * b * y⁻¹) * b⁻¹ := by
      rw [commutatorElement_def]
    rw [h2]
    exact (Tim79a.xOf V H).mul_mem h1 ((Tim79a.xOf V H).inv_mem hb)
  have hBW : a₁ * a₂ * ⁅y, (a₁ * a₂)⁻¹ * a⁆ * (a₁ * a₂)⁻¹ ∈ Tim79a.xOf V H := by
    have h1 : ⁅y, (a₁ * a₂)⁻¹ * a⁆ ∈ Tim79a.xOf V H := hyW _ hw
    have ha₁a₂H : a₁ * a₂ ∈ H := H.mul_mem (kOf_le V H ha₁K) (kOf_le V H ha₂K)
    exact ((Subgroup.mem_normalizer_iff.mp (Tim79a.H_le_normalizer_xOf V H ha₁a₂H)) _).mp h1
  have hcongB : ⁅y, a₁ * a₂⁆⁻¹ * ⁅y, a⁆ ∈ Tim79a.xOf V H := by
    rw [hB]
    have h2 : ⁅y, a₁ * a₂⁆⁻¹ * (⁅y, a₁ * a₂⁆ *
        (a₁ * a₂ * ⁅y, (a₁ * a₂)⁻¹ * a⁆ * (a₁ * a₂)⁻¹)) =
        a₁ * a₂ * ⁅y, (a₁ * a₂)⁻¹ * a⁆ * (a₁ * a₂)⁻¹ := by
      group
    rw [h2]
    exact hBW
  have hfin : ⁅y, a₁⁆⁻¹ * ⁅y, a⁆ =
      (⁅y, a₁⁆⁻¹ * ⁅y, a₁ * a₂⁆) * (⁅y, a₁ * a₂⁆⁻¹ * ⁅y, a⁆) := by
    group
  rw [hfin]
  exact (Tim79a.xOf V H).mul_mem hcongA hcongB


private theorem Sec45Shape.exists_mem_inf_Pc_commutator_congr {H : Subgroup G} {c y : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H c) (hcH : c ∈ H) (hyH : y ∈ H)
    (hy : y ∈ conjSubgroup c (Pc M V)) {a : G} (ha : a ∈ kOf V H) :
    ∃ a₁ ∈ Pc M V ⊓ kOf V H, ⁅y, a₁⁆⁻¹ * ⁅y, a⁆ ∈ Tim79a.xOf V H := by
  obtain ⟨a₁, ha₁, a₂, ha₂, hWa⟩ :=
    Sec45Shape.exists_mem_inf_Pc_mul_inv_mem_xOf h hS ha
  exact ⟨a₁, ha₁, Sec45Shape.commutatorElement_congr_of_mul_mem_xOf h hS hcH hyH hy ha₁ ha₂ hWa⟩

private theorem Sec45Shape.exists_mem_inf_Pc_kOf_mul_mem_xOf {H : Subgroup G} {c x y : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H c) (hcH : c ∈ H)
    (hy : y ∈ conjSubgroup c (Pc M V)) (hyK : y ∉ kOf V H)
    (hxy : ⁅y, x⁆ ∈ kOf V H)
    (hxcent : x ∈ Subgroup.centralizer (conjSubgroup c V : Set G)) :
    ∃ n ∈ Pc M V ⊓ kOf V H, ⁅y, n * x⁆ ∈ Tim79a.xOf V H := by
  classical
  obtain ⟨a, haK, ha⟩ := exists_mem_kOf_commutator_congr h hS hcH hy hyK hxy hxcent
  have hyH : y ∈ H := conjSubgroup_le_of_le_of_mem hS.Pc_le hcH hy
  obtain ⟨a₁, ha₁, hcongr⟩ := exists_mem_inf_Pc_commutator_congr h hS hcH hyH hy haK
  have hmain : ⁅y, a₁⁻¹ * x⁆ = a₁⁻¹ * (⁅y, a₁⁆⁻¹ * ⁅y, x⁆) * a₁ := by
    rw [commutatorElement_mul_right_eq_mul_conj, commutatorElement_inv_right]
    group
  have hprod : ⁅y, a₁⁆⁻¹ * ⁅y, x⁆ ∈ Tim79a.xOf V H := by
    have h1 : ⁅y, a₁⁆⁻¹ * ⁅y, x⁆ = (⁅y, a₁⁆⁻¹ * ⁅y, a⁆) * (⁅y, a⁆⁻¹ * ⁅y, x⁆) := by group
    rw [h1]
    exact (Tim79a.xOf V H).mul_mem hcongr ha
  refine ⟨a₁⁻¹, Subgroup.mem_inf.mpr ⟨(Pc M V).inv_mem ha₁.1, (kOf V H).inv_mem ha₁.2⟩, ?_⟩
  rw [hmain]
  simpa using ((Subgroup.mem_normalizer_iff.mp
    (Tim79a.H_le_normalizer_xOf V H (H.inv_mem (kOf_le V H ha₁.2))) _)).mp hprod

private theorem Sec45Shape.sup_kOf_commMemSubgroup_eq {H : Subgroup G} {c g x y n : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H c)
    (hyV : conjSubgroup y V ≠ V)
    (hy : y ∈ commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x))
    (hCle : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ≤
      commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x))
    (hPC : Pc M V = (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup c V : Set G)))
    (hCcK : Pc M V ⊓ Subgroup.centralizer (conjSubgroup c V : Set G) = Pc M V ⊓ kOf V H) :
    kOf V H ⊔ commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x) = H := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  set H₁ : Subgroup G :=
    commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x) with hH₁
  have hH₁H : H₁ ≤ H := commMemSubgroup_le _ _ _ _
  have hyH : y ∈ H := hH₁H hy
  have himgK : imgK V H (kOf V H) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨a, ha, rfl⟩ := (mem_imgK_iff).mp hz
    exact (piK_eq_one_iff a).mpr ha
  have himgP : imgK V H (Pc M V) ≤ imgK V H H₁ := by
    have h1 : imgK V H (Pc M V) =
        imgK V H (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊔
          imgK V H (Pc M V ⊓ Subgroup.centralizer (conjSubgroup c V : Set G)) := by
      conv_lhs => rw [hPC]
      rw [imgK_sup (inf_le_left.trans hS.Pc_le) (inf_le_left.trans hS.Pc_le)]
    rw [h1]
    refine sup_le (imgK_mono hCle) ?_
    rw [hCcK]
    exact (imgK_mono (inf_le_right : Pc M V ⊓ kOf V H ≤ kOf V H)).trans (himgK ▸ bot_le)
  have hconjH₁ : conjSubgroup y H₁ = H₁ :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hy)
  have himgPy : imgK V H (conjSubgroup y (Pc M V)) ≤ imgK V H H₁ := by
    rw [imgK_conjSubgroup hyH hS.Pc_le]
    calc conjSubgroup (piK V H ⟨y, hyH⟩) (imgK V H (Pc M V))
        ≤ conjSubgroup (piK V H ⟨y, hyH⟩) (imgK V H H₁) :=
          conjSubgroup_mono (g := piK V H ⟨y, hyH⟩) himgP
      _ = imgK V H H₁ := by rw [← imgK_conjSubgroup hyH hH₁H, hconjH₁]
  have hsup : imgK V H (Pc M V) ⊔ imgK V H (conjSubgroup y (Pc M V)) = ⊤ := by
    obtain ⟨a, ha⟩ := hS.exists_map_imgK_eq_conj_utri h ψ (x := 1) H.one_mem
    obtain ⟨b, hb⟩ := hS.exists_map_imgK_eq_conj_utri h ψ hyH
    simp only [conjSubgroup_one] at ha
    have hne : conjSubgroup a (utri F) ≠ conjSubgroup b (utri F) := by
      intro heq
      have h1 : (imgK V H (Pc M V)).map ψ.toMonoidHom =
          (imgK V H (conjSubgroup y (Pc M V))).map ψ.toMonoidHom := by
        rw [ha, hb, heq]
      have h2 : imgK V H (Pc M V) = imgK V H (conjSubgroup y (Pc M V)) := by
        refine Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective ?_
        simpa using h1
      exact hS.imgK_conj_ne h hyH hyV h2.symm
    have hmap : (imgK V H (Pc M V) ⊔ imgK V H (conjSubgroup y (Pc M V))).map ψ.toMonoidHom = ⊤ := by
      rw [Subgroup.map_sup, ha, hb, sup_conjSubgroup_utri_eq_top hne]
    refine Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective ?_
    rw [hmap, Subgroup.map_top_of_surjective _ ψ.surjective]
  have himgH₁ : imgK V H H₁ = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hsup]
    exact sup_le himgP himgPy
  have hsupK : H₁ ⊔ kOf V H = H ⊔ kOf V H :=
    (imgK_eq_iff_sup_kOf_eq hH₁H (le_refl H)).mp (by rw [himgH₁, imgK_self])
  rw [sup_comm (a := kOf V H) (b := H₁), hsupK, sup_eq_left.mpr (kOf_le V H)]


private theorem Sec45Shape.conj_commutator_eq {H : Subgroup G} {h₀ x₁ z a : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    (hz : ⁅z, x₁⁆ ∈ Tim79a.xOf V H) (hb : z * a * z⁻¹ ∈ kOf V H)
    (hKcent : kOf V H ≤ Subgroup.centralizer (Tim79a.xOf V H : Set G))
    (hbW : ⁅x₁, z * a * z⁻¹⁆ ∈ Tim79a.xOf V H) :
    z * ⁅x₁, a⁆ * z⁻¹ = ⁅x₁, z * a * z⁻¹⁆ := by
  have h1 : z * ⁅x₁, a⁆ * z⁻¹ = ⁅z * x₁ * z⁻¹, z * a * z⁻¹⁆ :=
    conjugate_commutatorElement x₁ a z
  rw [h1, show z * x₁ * z⁻¹ = ⁅z, x₁⁆ * x₁ from
    conj_eq_commutatorElement_mul (g₁ := z) (g₂ := x₁),
    commutatorElement_mul_left_eq_conj_mul]
  have h2 : ⁅⁅z, x₁⁆, z * a * z⁻¹⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (hKcent hb) ⁅z, x₁⁆ hz
  have h3 : ⁅z, x₁⁆ * ⁅x₁, z * a * z⁻¹⁆ * ⁅z, x₁⁆⁻¹ = ⁅x₁, z * a * z⁻¹⁆ := by
    have hab : Tim79a.xOf V H ≤ Subgroup.centralizer (Tim79a.xOf V H : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr (hS.isElemAbelian h).1
    have hcomm : ⁅z, x₁⁆ * ⁅x₁, z * a * z⁻¹⁆ = ⁅x₁, z * a * z⁻¹⁆ * ⁅z, x₁⁆ :=
      (Subgroup.mem_centralizer_iff.mp (hab hz) _ hbW).symm
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rw [h2, mul_one, h3]


private theorem Sec45Shape.le_commMemSubgroup_of_le_centralizer {H : Subgroup G} {h₀ g x n : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    (hn : n ∈ Pc M V) (hx1 : x ∈ conjSubgroup g V) :
    Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ≤
      commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x) := by
  intro c' hc'
  refine (mem_commMemSubgroup _ _ c').mpr ⟨hS.Pc_le hc'.1, ?_⟩
  have h1 : ⁅c', n⁆ ∈ V := by
    have hcc := Subgroup.commutator_mem_commutator hc'.1 hn
    rwa [hS.commutator_Pc h] at hcc
  have h2 : ⁅c', x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_centralizer_iff.mp hc'.2 x hx1).symm
  rw [commutatorElement_mul_right_eq_mul_conj, h2, mul_one, mul_assoc, mul_inv_cancel, mul_one]
  exact le_xOf_self V H h1


private theorem commutatorElementHom_range_eq_bot_or_eq_xOf {H : Subgroup G} {c g x n y : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H c)
    (hx1 : x ∈ conjSubgroup g V)
    (hnP : n ∈ Pc M V)
    (hPC : Pc M V = (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup c V : Set G)))
    (hCcK : Pc M V ⊓ Subgroup.centralizer (conjSubgroup c V : Set G) = Pc M V ⊓ kOf V H)
    (hyVne : conjSubgroup y V ≠ V)
    (hy : y ∈ commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x))
    (χ : ↥(commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x) ⊓
      kOf V H) →* ↥(Tim79a.xOf V H))
    (hχval : ∀ a, (Tim79a.xOf V H).subtype (χ a) = ⁅n * x, (a : G)⁆) :
    χ.range.map (Tim79a.xOf V H).subtype = ⊥ ∨
      χ.range.map (Tim79a.xOf V H).subtype = Tim79a.xOf V H := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  let W : Subgroup G := Tim79a.xOf V H
  let K : Subgroup G := kOf V H
  let H₁ : Subgroup G := commMemSubgroup H W (Tim79a.H_le_normalizer_xOf V H) (n * x)
  have hH₁H : H₁ ≤ H := commMemSubgroup_le _ _ _ _
  have hKcent : K ≤ Subgroup.centralizer (W : Set G) := xOf_le_centralizer_kOf hS
  by_cases hbot : χ.range.map W.subtype = ⊥
  · exact Or.inl hbot
  · refine Or.inr ?_
    have hW₁W : χ.range.map W.subtype ≤ W := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
      exact u.2
    have hH₁le : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ≤ H₁ :=
      Sec45Shape.le_commMemSubgroup_of_le_centralizer (h₀ := c) h hS hnP hx1
    have hsup : H = K ⊔ H₁ :=
      (Sec45Shape.sup_kOf_commMemSubgroup_eq (c := c) h hS hyVne hy hH₁le hPC hCcK).symm
    have hcentW₁ : K ≤ Subgroup.centralizer ((χ.range.map W.subtype : Subgroup G) : Set G) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro w' hw'
      exact Subgroup.mem_centralizer_iff.mp (hKcent hk) w' (hW₁W hw')
    have hKle : K ≤ Subgroup.normalizer (χ.range.map W.subtype : Set G) :=
      hcentW₁.trans (Subgroup.centralizer_le_normalizer _)
    have hstep : ∀ z ∈ H₁, ∀ w' ∈ χ.range.map W.subtype, z * w' * z⁻¹ ∈ χ.range.map W.subtype := by
      intro z hz w' hw'
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw'
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hu
      have hzK : z ∈ H := hH₁H hz
      have hb : z * (a : G) * z⁻¹ ∈ H₁ ⊓ K :=
        Subgroup.mem_inf.mpr ⟨H₁.mul_mem (H₁.mul_mem hz a.2.1) (H₁.inv_mem hz),
          (hS.quotModHyp h).conj z hzK (a : G) a.2.2⟩
      refine Subgroup.mem_map.mpr ⟨χ ⟨z * (a : G) * z⁻¹, hb⟩, ⟨_, rfl⟩, ?_⟩
      rw [hχval, hχval]
      exact (Sec45Shape.conj_commutator_eq (h₀ := c) h hS
        ((mem_commMemSubgroup _ _ z).mp hz).2 hb.2 hKcent
        (by
          have h := (mem_commMemSubgroup _ _ (z * (a : G) * z⁻¹)).mp
            ((inf_le_left : H₁ ⊓ K ≤ H₁) hb) |>.2
          rw [← commutatorElement_inv]
          exact (Tim79a.xOf V H).inv_mem h)).symm
    have hH₁le' : H₁ ≤ Subgroup.normalizer (χ.range.map W.subtype : Set G) := by
      intro z hz
      rw [Subgroup.mem_normalizer_iff]
      intro w'
      exact ⟨hstep z hz w', fun hw' => by
        have h1 := hstep z⁻¹ (H₁.inv_mem hz) (z * w' * z⁻¹) hw'
        rwa [show z⁻¹ * (z * w' * z⁻¹) * (z⁻¹)⁻¹ = w' by group] at h1⟩
    have hN : H ≤ Subgroup.normalizer (χ.range.map W.subtype : Set G) := fun z hz =>
      (sup_le hKle hH₁le') (hsup ▸ hz)
    exact Sec45Shape.eq_xOf_of_le h hS hW₁W hbot hN


private theorem mem_subSec_secCent_of_mem_inf_Pc_commutator {H : Subgroup G} {c x n c' : G}
    (hS : Sec45Shape M V H c)
    (hs : CFSG.Timmesfeld.Bridge.QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal]
    [Module (ZMod 2) (SecMod hs)]
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F))
    (hσ : Sec2.IsNatSumModule (repSec hs hs.comm SL(2, F) ψ))
    (hA2 : ∀ z ∈ (imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F)), z * z = 1)
    (hAcard : Nat.card ((imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F))) = Fintype.card F)
    (hc'P : c' ∈ Pc M V)
    (a : ↥(commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x) ⊓
      kOf V H))
    (hbK : ⁅c', (a : G)⁆ ∈ kOf V H) :
    SecMod.mk hs ⟨⁅c', (a : G)⁆, hbK⟩ ∈ subSec hs (secCent hs (Pc M V) hS.Pc_le) := by
  have hA1 : (⟨⁅c', (a : G)⁆, hbK⟩ : ↥(kOf V H)) =
      ⟨c' * (a : G) * c'⁻¹, hs.conj c' (hS.Pc_le hc'P) (a : G) a.2.2⟩ *
        ⟨(a : G), a.2.2⟩⁻¹ := Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rfl)
  have hmkc : SecMod.mk hs ⟨⁅c', (a : G)⁆, hbK⟩ ∈
      commSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F))) := by
    refine range_le_commSub (A := (imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F)))
      (a := ψ (piK V H ⟨c', hS.Pc_le hc'P⟩))
      (Subgroup.mem_map_of_mem (ψ : HBar V H →* SL(2, F))
        (mem_imgK_iff.mpr ⟨⟨c', hS.Pc_le hc'P⟩, hc'P, rfl⟩)) ?_
    refine ⟨SecMod.mk hs ⟨(a : G), a.2.2⟩, ?_⟩
    rw [LinearMap.sub_apply, Module.End.one_apply, repSec_apply_piK_mk, hA1, SecMod.mk_mul,
      SecMod.mk_inv, sub_eq_add_neg]
  have hfix : SecMod.mk hs ⟨⁅c', (a : G)⁆, hbK⟩ ∈
      fixedSub (repSec hs hs.comm SL(2, F) ψ)
        ((imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F))) :=
    Sec2.IsNatSumModule.commSub_le_fixedSub hσ hA2 hAcard hmkc
  rw [fixedSub_repSec hs hs.comm ψ hS.Pc_le] at hfix
  exact hfix

private theorem imgK_map_isElemAbelian_and_card {H : Subgroup G} {c : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H c)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    (hl : Fintype.card F = 2 ^ (2 * l)) (ψ : HBar V H ≃* SL(2, F)) :
    (∀ z ∈ (imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F)), z * z = 1) ∧
      Nat.card ((imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F))) = Fintype.card F := by
  constructor
  · rintro z ⟨z', hz', rfl⟩
    have h := (RootHyp.isElemAbelian_imgK h hS.Pc_le hS.le_pCore).2 z' hz'
    rw [← map_mul]
    exact (show ψ.toMonoidHom (z' * z') = 1 by simpa [pow_two] using congrArg ψ h)
  · have h1 : Nat.card ((imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F))) =
        Nat.card (imgK V H (Pc M V)) :=
      Subgroup.card_map_of_injective (f := (ψ : HBar V H →* SL(2, F))) ψ.injective
    rw [h1, RootHyp.card_imgK_eq_two_pow h hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ hl, hl]

private theorem commutatorElement_commutatorElementHom_eq_one {H : Subgroup G} {c g x n : G}
    {H₁ : Subgroup G} (h : RootHyp M V) (hS : Sec45Shape M V H c)
    (hs : CFSG.Timmesfeld.Bridge.QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal]
    [Module (ZMod 2) (SecMod hs)]
    (hKcent : kOf V H ≤ Subgroup.centralizer (Tim79a.xOf V H : Set G))
    (hH₁H : H₁ ≤ H) (hH₁le : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ≤ H₁)
    (hH₁comm : ∀ z ∈ H₁, ⁅z, n * x⁆ ∈ Tim79a.xOf V H)
    (b : ↥(H₁ ⊓ kOf V H)) (hb2 : (b : G) ∈ kOf V H)
    (hsec : (b : G) ∈ secCent hs (Pc M V) hS.Pc_le)
    (χ : ↥(H₁ ⊓ kOf V H) →* ↥(Tim79a.xOf V H))
    (hχval : ∀ a, (Tim79a.xOf V H).subtype (χ a) = ⁅n * x, (a : G)⁆)
    (hχW : ∀ (z : G) (hz : z ∈ H₁ ⊓ kOf V H), z ∈ Tim79a.xOf V H →
      (Tim79a.xOf V H).subtype (χ ⟨z, hz⟩) = 1) :
    ∀ p' ∈ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G),
      ⁅p', (Tim79a.xOf V H).subtype (χ b)⁆ = 1 := by
  intro p' hp'
  have hp'P : p' ∈ Pc M V := (Subgroup.mem_inf.mp hp').1
  have hp'H₁ : p' ∈ H₁ := hH₁le hp'
  have hpb : p' * (b : G) * p'⁻¹ ∈ H₁ ⊓ kOf V H := by
    refine Subgroup.mem_inf.mpr ⟨?_, hs.conj p' (hH₁H hp'H₁) (b : G) hb2⟩
    have h1 : p' * (b : G) ∈ H₁ := H₁.mul_mem hp'H₁ b.2.1
    have h := H₁.mul_mem h1 (H₁.inv_mem hp'H₁)
    simpa [mul_assoc] using h
  have hbH₁ : (b : G) ∈ H₁ := b.2.1
  have hpb' : ⁅p', (b : G)⁆ ∈ H₁ ⊓ kOf V H := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : p' * (b : G) ∈ H₁ := H₁.mul_mem hp'H₁ hbH₁
      have h2 : p' * (b : G) * p'⁻¹ ∈ H₁ := by
        have h := H₁.mul_mem h1 (H₁.inv_mem hp'H₁)
        simpa [mul_assoc] using h
      have h := H₁.mul_mem h2 (H₁.inv_mem hbH₁)
      simpa [commutatorElement_def, mul_assoc] using h
    · have h1 : p' * (b : G) * p'⁻¹ ∈ kOf V H := hs.conj p' (hH₁H hp'H₁) (b : G) hb2
      have h := (kOf V H).mul_mem h1 ((kOf V H).inv_mem hb2)
      simpa [commutatorElement_def, mul_assoc] using h
  have hconj : p' * (Tim79a.xOf V H).subtype (χ b) * p'⁻¹ =
      (Tim79a.xOf V H).subtype (χ ⟨p' * (b : G) * p'⁻¹, hpb⟩) := by
    rw [hχval b, hχval ⟨p' * (b : G) * p'⁻¹, hpb⟩]
    refine Sec45Shape.conj_commutator_eq h hS (hH₁comm p' hp'H₁)
      (Subgroup.mem_inf.mp hpb).2 hKcent ?_
    have h := hH₁comm (p' * (b : G) * p'⁻¹) ((inf_le_left : H₁ ⊓ kOf V H ≤ H₁) hpb)
    rw [← commutatorElement_inv]
    exact (Tim79a.xOf V H).inv_mem h
  have hprod : (Tim79a.xOf V H).subtype (χ ⟨p' * (b : G) * p'⁻¹, hpb⟩) =
      (Tim79a.xOf V H).subtype (χ ⟨⁅p', (b : G)⁆, hpb'⟩) *
        (Tim79a.xOf V H).subtype (χ b) := by
    have harg : (⟨⁅p', (b : G)⁆, hpb'⟩ : ↥(H₁ ⊓ kOf V H)) * b =
        ⟨p' * (b : G) * p'⁻¹, hpb⟩ := Subtype.ext (by
          simp only [Subgroup.coe_mul, commutatorElement_def]
          group)
    rw [← harg, map_mul]
    rfl
  have hzb : ⁅p', (b : G)⁆ ∈ Tim79a.xOf V H := by
    have h := ((mem_secCent hs hS.Pc_le).mp hsec).2 p' hp'P
    rw [← commutatorElement_inv]
    exact (Tim79a.xOf V H).inv_mem h
  rw [commutatorElement_def, hconj, hprod, hχW _ hpb' hzb, one_mul, mul_inv_cancel]

private theorem false_of_imgK_eq_bot {H : Subgroup G} {c g y w : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H c) (hyH : y ∈ H)
    (hyVne : conjSubgroup y V ≠ V) (hwV' : w ∈ conjSubgroup y V) (hw1' : w ≠ 1)
    (hPC : Pc M V = (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup c V : Set G)))
    (hCcK : Pc M V ⊓ Subgroup.centralizer (conjSubgroup c V : Set G) = Pc M V ⊓ kOf V H)
    (hkey : ∀ c' ∈ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G), ⁅c', w⁆ ∈ V) :
    False := by
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  have hCK : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ≤ kOf V H := by
    intro c' hc'
    exact Sec45Shape.mem_kOf_of_commutator_mem h hS hyH hyVne hwV' hw1'
      (Subgroup.mem_inf.mp hc').1 (hkey c' hc')
  have hPK : Pc M V ≤ kOf V H := by
    rw [hPC, hCcK]
    exact sup_le hCK inf_le_right
  have himg : imgK V H (Pc M V) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨p, hp, rfl⟩ := (mem_imgK_iff).mp hz
    exact (piK_eq_one_iff p).mpr (hPK hp)
  have hcard := RootHyp.card_imgK_eq_two_pow h hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ hl
  rw [himg, Nat.card_eq_fintype_card, Fintype.card_ofSubsingleton] at hcard
  have hl1 : 1 ≤ l := hw.one_le
  have h2 : 2 ≤ 2 ^ (2 * l) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * l) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

private theorem commutatorElement_mem_V_of_mem_inf_Pc {H : Subgroup G} {c g x n c' w : G}
    {H₁ : Subgroup G} (h : RootHyp M V) (hS : Sec45Shape M V H c)
    (hs : CFSG.Timmesfeld.Bridge.QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H))
    [((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal]
    [Module (ZMod 2) (SecMod hs)]
    (hKcent : kOf V H ≤ Subgroup.centralizer (Tim79a.xOf V H : Set G))
    (hH₁le : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ≤ H₁)
    (hH₁comm : ∀ z ∈ H₁, ⁅z, n * x⁆ ∈ Tim79a.xOf V H)
    (hPC : Pc M V = (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup c V : Set G)))
    (hCcK : Pc M V ⊓ Subgroup.centralizer (conjSubgroup c V : Set G) = Pc M V ⊓ kOf V H)
    (χ : ↥(H₁ ⊓ kOf V H) →* ↥(Tim79a.xOf V H))
    (hχval : ∀ a, (Tim79a.xOf V H).subtype (χ a) = ⁅n * x, (a : G)⁆)
    (hc' : c' ∈ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G))
    (a : ↥(H₁ ⊓ kOf V H)) (b : ↥(H₁ ⊓ kOf V H)) (hb : ⁅c', (a : G)⁆ ∈ H₁ ⊓ kOf V H)
    (hbdef : b = ⟨⁅c', (a : G)⁆, hb⟩) (haw : (Tim79a.xOf V H).subtype (χ a) = w)
    (hC : ∀ p' ∈ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G),
      ⁅p', (Tim79a.xOf V H).subtype (χ b)⁆ = 1) :
    ⁅c', w⁆ ∈ V := by
  have hc'P : c' ∈ Pc M V := (Subgroup.mem_inf.mp hc').1
  have hc'H₁ : c' ∈ H₁ := hH₁le hc'
  have hcent : (Tim79a.xOf V H).subtype (χ b) ∈ Subgroup.centralizer (Pc M V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hX : Pc M V ≤ Subgroup.centralizer
        ({(Tim79a.xOf V H).subtype (χ b)} : Set G) := by
      rw [hPC]
      refine sup_le ?_ ?_
      · intro p' hp'
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact commutatorElement_eq_one_iff_mul_comm.mp (hC p' hp')
      · intro p' hp'
        rw [hCcK] at hp'
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (hKcent (Subgroup.mem_inf.mp hp').2) _
          (χ b).2).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hX hp)
  have hbV : (Tim79a.xOf V H).subtype (χ b) ∈ V := by
    have hmem : (Tim79a.xOf V H).subtype (χ b) ∈
        Tim79a.xOf V H ⊓ Subgroup.centralizer (Pc M V : Set G) := ⟨(χ b).2, hcent⟩
    rwa [show Tim79a.xOf V H ⊓ Subgroup.centralizer (Pc M V : Set G) = V from
      h.xOf_inf_centralizer_Pc_eq_V] at hmem
  have hceq : ⁅c', w⁆ = (Tim79a.xOf V H).subtype (χ b) := by
    have hc'ac' : c' * (a : G) * c'⁻¹ ∈ H₁ := by
      have h := H₁.mul_mem (H₁.mul_mem hc'H₁ a.2.1) (H₁.inv_mem hc'H₁)
      simpa [mul_assoc] using h
    have hc'ac'K : c' * (a : G) * c'⁻¹ ∈ H₁ ⊓ kOf V H :=
      Subgroup.mem_inf.mpr ⟨hc'ac', hs.conj c' (hS.Pc_le hc'P) (a : G) a.2.2⟩
    have hzust : ⁅n * x, c' * (a : G) * c'⁻¹⁆ ∈ Tim79a.xOf V H := by
      have h := hH₁comm (c' * (a : G) * c'⁻¹) hc'ac'
      rw [← commutatorElement_inv]
      exact (Tim79a.xOf V H).inv_mem h
    have hconj : c' * (Tim79a.xOf V H).subtype (χ a) * c'⁻¹ =
        (Tim79a.xOf V H).subtype (χ ⟨c' * (a : G) * c'⁻¹, hc'ac'K⟩) := by
      rw [hχval a, hχval ⟨c' * (a : G) * c'⁻¹, hc'ac'K⟩]
      exact Sec45Shape.conj_commutator_eq h hS (hH₁comm c' hc'H₁)
        (Subgroup.mem_inf.mp hc'ac'K).2 hKcent hzust
    have harg : (⟨c' * (a : G) * c'⁻¹, hc'ac'K⟩ : ↥(H₁ ⊓ kOf V H)) * a⁻¹ = b := by
      subst hbdef
      apply Subtype.ext
      show c' * (a : G) * c'⁻¹ * ((a : G)⁻¹) = ⁅c', (a : G)⁆
      rw [commutatorElement_def]
    have hinner : χ ⟨c' * (a : G) * c'⁻¹, hc'ac'K⟩ * (χ a)⁻¹ = χ b := by
      rw [show (χ a)⁻¹ = χ a⁻¹ from (map_inv χ a).symm, ← map_mul, harg]
    calc ⁅c', w⁆ = c' * (Tim79a.xOf V H).subtype (χ a) * c'⁻¹ *
          (Tim79a.xOf V H).subtype (χ a)⁻¹ := by
            rw [commutatorElement_def, ← haw]
            simp only [map_inv, Subgroup.coe_inv]
      _ = (Tim79a.xOf V H).subtype (χ ⟨c' * (a : G) * c'⁻¹, hc'ac'K⟩) *
          (Tim79a.xOf V H).subtype (χ a)⁻¹ := by rw [hconj]
      _ = (Tim79a.xOf V H).subtype
          (χ ⟨c' * (a : G) * c'⁻¹, hc'ac'K⟩ * (χ a)⁻¹) := rfl
      _ = (Tim79a.xOf V H).subtype (χ b) := by rw [hinner]
  exact hceq ▸ hbV

private theorem false_of_commutatorElementHom_range_eq_xOf {H : Subgroup G} {c g x n y : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H c)
    (hxW : x ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G))
    (hx1 : x ∈ conjSubgroup g V)
    (hnP : n ∈ Pc M V) (hnK : n ∈ kOf V H)
    (hPC : Pc M V = (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup c V : Set G)))
    (hCcK : Pc M V ⊓ Subgroup.centralizer (conjSubgroup c V : Set G) = Pc M V ⊓ kOf V H)
    (hyH : y ∈ H) (hyVne : conjSubgroup y V ≠ V)
    (χ : ↥(commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x) ⊓
      kOf V H) →* ↥(Tim79a.xOf V H))
    (hχval : ∀ a, (Tim79a.xOf V H).subtype (χ a) = ⁅n * x, (a : G)⁆)
    (htop : χ.range.map (Tim79a.xOf V H).subtype = Tim79a.xOf V H) : False := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  let W : Subgroup G := Tim79a.xOf V H
  let K : Subgroup G := kOf V H
  let H₁ : Subgroup G := commMemSubgroup H W (Tim79a.H_le_normalizer_xOf V H) (n * x)
  have hKq := hS.quotModHyp h
  haveI hKnorm : ((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal := hKq.normal
  haveI hmod : Module (ZMod 2) (SecMod hKq) := SecMod.module hKq hw.sq_mem
  have hσ : Sec2.IsNatSumModule (repSec hKq hKq.comm SL(2, F) ψ) :=
    hw.natSum hKq (inferInstance : Module (ZMod 2) (SecMod hKq))
  have hKcent : K ≤ Subgroup.centralizer (W : Set G) := xOf_le_centralizer_kOf hS
  have hx₁W : (n * x) ∈ Subgroup.centralizer (W : Set G) :=
    (Subgroup.centralizer (W : Set G)).mul_mem (hKcent hnK) hxW
  have hH₁H : H₁ ≤ H := commMemSubgroup_le _ _ _ _
  have hH₁le : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ≤ H₁ :=
    Sec45Shape.le_commMemSubgroup_of_le_centralizer (h₀ := c) h hS hnP hx1
  obtain ⟨w, a, hw1', haw⟩ :=
    exists_mem_conj_eq_of_map_range_eq_xOf (H₁ := H₁ ⊓ K) h hyH χ htop
  have hwV' : (w : G) ∈ conjSubgroup y V := w.2
  have hwW : (w : G) ∈ W := conjSubgroup_le_xOf_of_mem hyH hwV'
  obtain ⟨hA2, hAcard⟩ := imgK_map_isElemAbelian_and_card h hS hl ψ
  have hχW : ∀ (z : G) (hz : z ∈ H₁ ⊓ K), z ∈ W → (Tim79a.xOf V H).subtype (χ ⟨z, hz⟩) = 1 := by
    intro z hz hzW
    rw [hχval, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp hx₁W z hzW).symm
  have hkey : ∀ c' ∈ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G),
      ⁅c', (w : G)⁆ ∈ V := by
    intro c' hc'
    have hc'H₁ : c' ∈ H₁ := hH₁le hc'
    have hc'P : c' ∈ Pc M V := (Subgroup.mem_inf.mp hc').1
    have hb : ⁅c', (a : G)⁆ ∈ H₁ ⊓ K := by
      have hca : c' * (a : G) ∈ H₁ := H₁.mul_mem hc'H₁ a.2.1
      have h1 : c' * (a : G) * c'⁻¹ ∈ H₁ := by
        have h := H₁.mul_mem hca (H₁.inv_mem hc'H₁)
        simpa [mul_assoc] using h
      have h2 : (a : G)⁻¹ ∈ H₁ := H₁.inv_mem a.2.1
      have h3 : c' * (a : G) * c'⁻¹ * (a : G)⁻¹ ∈ H₁ := by
        have h := H₁.mul_mem h1 h2
        simpa [mul_assoc] using h
      refine Subgroup.mem_inf.mpr ⟨h3, ?_⟩
      show c' * (a : G) * c'⁻¹ * (a : G)⁻¹ ∈ K
      have h1 : c' * (a : G) * c'⁻¹ ∈ K := hKq.conj c' (hS.Pc_le hc'P) (a : G) a.2.2
      have h2 : (a : G)⁻¹ ∈ K := K.inv_mem a.2.2
      have := K.mul_mem h1 h2
      simpa [mul_assoc] using this
    let b : ↥(H₁ ⊓ K) := ⟨⁅c', (a : G)⁆, hb⟩
    have hb1 : ⁅c', (a : G)⁆ ∈ H₁ := (Subgroup.mem_inf.mp hb).1
    have hb2 : ⁅c', (a : G)⁆ ∈ K := (Subgroup.mem_inf.mp hb).2
    have bH₁ : (b : G) ∈ H₁ := (Subgroup.mem_inf.mp b.2).1
    have bK : (b : G) ∈ K := (Subgroup.mem_inf.mp b.2).2
    have hsec : (b : G) ∈ secCent hKq (Pc M V) hS.Pc_le :=
      (mk_mem_subSec_iff hKq (le_secCent hKq hS.Pc_le)).mp
        (mem_subSec_secCent_of_mem_inf_Pc_commutator (hs := hKq) hS ψ hσ hA2 hAcard hc'P a hb2)
    have hC : ∀ p' ∈ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G),
        ⁅p', (Tim79a.xOf V H).subtype (χ b)⁆ = 1 :=
      commutatorElement_commutatorElementHom_eq_one (H₁ := H₁) h hS hKq hKcent hH₁H
        hH₁le (fun z hz => (mem_commMemSubgroup _ _ z).mp hz |>.2) b hb2 hsec χ hχval hχW
    exact commutatorElement_mem_V_of_mem_inf_Pc (H₁ := H₁) h hS hKq hKcent hH₁le
      (fun z hz => (mem_commMemSubgroup _ _ z).mp hz |>.2) hPC hCcK χ hχval hc' a b hb rfl haw hC
  exact false_of_imgK_eq_bot h hS hyH hyVne hwV' hw1' hPC hCcK hkey


private theorem commutator_eq_one_of_mem_inf {H : Subgroup G} {c g x n y : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H c)
    (hxW : x ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G))
    (hx1 : x ∈ conjSubgroup g V)
    (hnP : n ∈ Pc M V) (hnK : n ∈ kOf V H)
    (hPC : Pc M V = (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup c V : Set G)))
    (hCcK : Pc M V ⊓ Subgroup.centralizer (conjSubgroup c V : Set G) = Pc M V ⊓ kOf V H)
    (hyH : y ∈ H)
    (hyVne : conjSubgroup y V ≠ V)
    (hy : y ∈ commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x)) :
    ∀ k ∈ commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x) ⊓
        kOf V H, k * (n * x) = (n * x) * k := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  let W : Subgroup G := Tim79a.xOf V H
  let K : Subgroup G := kOf V H
  let H₁ : Subgroup G := commMemSubgroup H W (Tim79a.H_le_normalizer_xOf V H) (n * x)
  have hKcent : K ≤ Subgroup.centralizer (W : Set G) := xOf_le_centralizer_kOf hS
  have hx₁W : (n * x) ∈ Subgroup.centralizer (W : Set G) :=
    (Subgroup.centralizer (W : Set G)).mul_mem (hKcent hnK) hxW
  have hZA : W ≤ Subgroup.centralizer ((H₁ ⊓ K : Subgroup G) : Set G) := by
    intro w' hw'
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hKcent (Subgroup.mem_inf.mp ha).2) w' hw').symm
  have hxA : ∀ a ∈ H₁ ⊓ K, ⁅n * x, a⁆ ∈ W := by
    intro a ha
    have h1 : ⁅a, n * x⁆ ∈ W := (mem_commMemSubgroup _ _ a).mp (Subgroup.mem_inf.mp ha).1 |>.2
    rw [← commutatorElement_inv]
    exact (Tim79a.xOf V H).inv_mem h1
  let χ : ↥(H₁ ⊓ K) →* ↥W := commutatorElementHom (n * x) hZA hxA
  have hχval : ∀ a, (Tim79a.xOf V H).subtype (χ a) = ⁅n * x, (a : G)⁆ := fun a => rfl
  intro k hk
  rcases commutatorElementHom_range_eq_bot_or_eq_xOf (c := c) h hS hx1 hnP hPC hCcK
    hyVne hy χ hχval with hbot | htop
  · have hχ1 : ∀ a : ↥(H₁ ⊓ K), χ a = 1 := by
      intro a
      apply Subtype.ext
      have hmem : (χ a : G) ∈ Subgroup.map W.subtype χ.range :=
        Subgroup.mem_map_of_mem W.subtype (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    have h2 : ⁅n * x, k⁆ = 1 := by
      have h3 : (Tim79a.xOf V H).subtype (χ ⟨k, hk⟩) = 1 := by
        rw [hχ1 ⟨k, hk⟩]
        rfl
      rw [← hχval ⟨k, hk⟩]
      exact h3
    have h4 : ⁅k, n * x⁆ = 1 := by
      rw [show ⁅k, n * x⁆ = ⁅n * x, k⁆⁻¹ from
        (commutatorElement_inv (g₁ := n * x) (g₂ := k)).symm, h2, inv_one]
    exact commutatorElement_eq_one_iff_mul_comm.mp h4
  · exact (false_of_commutatorElementHom_range_eq_xOf (c := c) h hS hxW hx1 hnP hnK hPC hCcK
      hyH hyVne χ hχval htop).elim



private theorem Sec45Shape.of_conjSubgroup_Pc_eq {H : Subgroup G} {h₀ y₀ : G}
    (hSh : Sec45Shape M V H h₀)
    (h : conjSubgroup y₀ (Pc M V) = conjSubgroup h₀ (Pc M V)) :
    Sec45Shape M V H y₀ :=
  { hH := by rw [hSh.hH, h]
    mem := hSh.mem
    le_pCore := hSh.le_pCore
    kFact := by
      unfold KFactorization
      rw [h]
      exact hSh.kFact
    shape := hSh.shape }


private def PcModuloV (h : RootHyp M V) (w : G) : Subgroup G where
  carrier := {p | p ∈ Pc M V ∧ ⁅p, w⁆ ∈ V}
  one_mem' := ⟨(Pc M V).one_mem, by simp⟩
  mul_mem' := by
    rintro p q ⟨hpP, hp⟩ ⟨hqP, hq⟩
    refine ⟨(Pc M V).mul_mem hpP hqP, ?_⟩
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact V.mul_mem
      ((Subgroup.mem_normalizer_iff.mp (h.toHyp.le_normalizer (h.toHyp.Pc_le_M hpP))
        ⁅q, w⁆).mp hq) hp
  inv_mem' := by
    rintro p ⟨hpP, hp⟩
    refine ⟨(Pc M V).inv_mem hpP, ?_⟩
    rw [commutatorElement_inv_left]
    have h1 : ⁅w, p⁆ ∈ V := by
      rw [show ⁅w, p⁆ = ⁅p, w⁆⁻¹ from (commutatorElement_inv (g₁ := p) (g₂ := w)).symm]
      exact V.inv_mem hp
    simpa using (Subgroup.mem_normalizer_iff.mp
      (h.toHyp.le_normalizer (h.toHyp.Pc_le_M ((Pc M V).inv_mem hpP))) ⁅w, p⁆).mp h1

private theorem le_PcModuloV_of_le_centralizer {H : Subgroup G} {h₀ g x n w : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    (hC : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ≤
      commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x))
    (hx : x ∈ conjSubgroup g V) (hnP : n ∈ Pc M V)
    (hx₂ : w⁻¹ * (n * x) ∈ Subgroup.centralizer
      (commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x) : Set G)) :
    Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ≤ PcModuloV h w := by
  intro c' hc'
  have hc'P : c' ∈ Pc M V := (Subgroup.mem_inf.mp hc').1
  have hc'C : c' ∈ Subgroup.centralizer (conjSubgroup g V : Set G) := (Subgroup.mem_inf.mp hc').2
  have hc'H₁ : c' ∈ commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x) :=
    hC hc'
  have hx₁ : ⁅c', n * x⁆ ∈ V := by
    have h1 : ⁅c', n⁆ ∈ V := by
      have hmem := Subgroup.commutator_mem_commutator hc'P hnP
      rwa [hS.commutator_Pc h] at hmem
    have h2 : ⁅c', x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp hc'C x hx).symm
    have h3 : ⁅c', n * x⁆ = ⁅c', n⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, h2]
      group
    rw [h3]
    exact h1
  have hx₂c : c' * (w⁻¹ * (n * x)) = (w⁻¹ * (n * x)) * c' :=
    Subgroup.mem_centralizer_iff.mp hx₂ c' hc'H₁
  have hcomm : ⁅c', w⁻¹ * (n * x)⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr hx₂c
  have hcomm' : ⁅c', (w⁻¹ * (n * x))⁻¹⁆ = 1 := by
    rw [commutatorElement_inv_right,
      show ⁅(w⁻¹ * (n * x)), c'⁆ = ⁅c', w⁻¹ * (n * x)⁆⁻¹ from
        (commutatorElement_inv (g₁ := c') (g₂ := w⁻¹ * (n * x))).symm, hcomm]
    group
  have hw_eq : ⁅c', w⁆ = ⁅c', n * x⁆ := by
    have hw : w = (n * x) * (w⁻¹ * (n * x))⁻¹ := by group
    rw [hw, commutatorElement_mul_right_eq_mul_conj, hcomm', mul_one]
    group
  exact ⟨hc'P, by rw [hw_eq]; exact hx₁⟩

private theorem le_PcModuloV_of_le_kOf {H : Subgroup G} {w : G}
    (h : RootHyp M V) (hwW : w ∈ Tim79a.xOf V H)
    (hZW : Tim79a.xOf V H ≤ Subgroup.centralizer (kOf V H : Set G)) :
    Pc M V ⊓ kOf V H ≤ PcModuloV h w := by
  intro k' hk'
  refine ⟨(Subgroup.mem_inf.mp hk').1, ?_⟩
  have hcomm : k' * w = w * k' :=
    Subgroup.mem_centralizer_iff.mp (hZW hwW) k' (Subgroup.mem_inf.mp hk').2
  have h1 : ⁅k', w⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  rw [h1]
  exact V.one_mem

private theorem commutatorElement_mem_V_of_mem_Pc {H : Subgroup G} {h₀ g x n w : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    (hPC : Pc M V = (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h₀ V : Set G)))
    (hCcK : Pc M V ⊓ Subgroup.centralizer (conjSubgroup h₀ V : Set G) =
      Pc M V ⊓ kOf V H)
    (hwW : w ∈ Tim79a.xOf V H)
    (hC : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ≤
      commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x))
    (hx : x ∈ conjSubgroup g V) (hnP : n ∈ Pc M V)
    (hx₂ : w⁻¹ * (n * x) ∈ Subgroup.centralizer
      (commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x) : Set G)) :
    ∀ p ∈ Pc M V, ⁅p, w⁆ ∈ V := by
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  have hZW : Tim79a.xOf V H ≤ Subgroup.centralizer (kOf V H : Set G) := by
    rw [← hw.center_K]
    exact inf_le_right
  have hsub : Pc M V ≤ PcModuloV h w := by
    rw [hPC, hCcK]
    exact sup_le (le_PcModuloV_of_le_centralizer h hS hC hx hnP hx₂)
      (le_PcModuloV_of_le_kOf h hwW hZW)
  exact fun p hp => (hsub hp).2

private theorem mem_Pc_of_mem_xOf_centralizer {H : Subgroup G} {h₀ g x n w : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    (hPC : Pc M V = (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h₀ V : Set G)))
    (hCcK : Pc M V ⊓ Subgroup.centralizer (conjSubgroup h₀ V : Set G) =
      Pc M V ⊓ kOf V H)
    (hwW : w ∈ Tim79a.xOf V H)
    (hC : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ≤
      commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x))
    (hx : x ∈ conjSubgroup g V) (hnP : n ∈ Pc M V)
    (hx₂ : w⁻¹ * (n * x) ∈ Subgroup.centralizer
      (commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x) : Set G)) :
    w ∈ Pc M V := by
  have hwK : w ∈ kOf V H := h.xOf_le_kOf hS.Pc_le hS.le_pCore hwW
  refine Sec45Shape.mem_Pc_of_commutator_mem h hS (hS.kOf_le_M h hwK) ?_
    (commutatorElement_mem_V_of_mem_Pc h hS hPC hCcK hwW hC hx hnP hx₂)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 : w ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G) := by
    have hab : Tim79a.xOf V H ≤ Subgroup.centralizer (Tim79a.xOf V H : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr (hS.isElemAbelian h).1
    exact hab hwW
  exact (Subgroup.mem_centralizer_iff.mp h1 v (le_xOf_self V H hv))

private theorem exists_mem_Pc_inf_kOf_mul_mem_centralizer {H : Subgroup G} {h₀ g x n y : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    (hPC : Pc M V = (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h₀ V : Set G)))
    (hCcK : Pc M V ⊓ Subgroup.centralizer (conjSubgroup h₀ V : Set G) =
      Pc M V ⊓ kOf V H)
    (hnP : n ∈ Pc M V) (hnK : n ∈ kOf V H) (hx : x ∈ conjSubgroup g V)
    (hC : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ≤
      commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x))
    (hsup : kOf V H ⊔
      commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x) = H)
    (hcomm : ∀ k ∈
      commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x) ⊓ kOf V H,
      k * (n * x) = (n * x) * k) :
    ∃ p₀ ∈ Pc M V ⊓ kOf V H, ∃ x₂ : G, x = p₀ * x₂ ∧
      x₂ ∈ Subgroup.centralizer
        (commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x) : Set G) := by
  let H₁ : Subgroup G :=
    commMemSubgroup H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x)
  obtain ⟨w, hwW, hwx₂⟩ := Sec45Shape.exists_mem_xOf_inv_mul_mem_centralizer (L := H₁)
    h hS (commMemSubgroup_le H (Tim79a.xOf V H) (Tim79a.H_le_normalizer_xOf V H) (n * x))
    hsup hcomm (fun z hz => (mem_commMemSubgroup _ _ z).mp hz |>.2)
  have hwP : w ∈ Pc M V := mem_Pc_of_mem_xOf_centralizer h hS hPC hCcK hwW hC hx hnP hwx₂
  have hwK : w ∈ kOf V H := h.xOf_le_kOf hS.Pc_le hS.le_pCore hwW
  refine ⟨n⁻¹ * w, Subgroup.mem_inf.mpr ⟨(Pc M V).mul_mem ((Pc M V).inv_mem hnP) hwP,
    (kOf V H).mul_mem ((kOf V H).inv_mem hnK) hwK⟩, w⁻¹ * (n * x), ?_, hwx₂⟩
  group

theorem Sec5Hyp.s512_split (hS : Sec5Hyp M V) {g h : G}
    (hU' : conjSubgroup h V ∈ sigmaSet M V)
    (hc : ⁅conjSubgroup g V, conjSubgroup h V⁆ = ⊥)
    (hKF : ∀ u ∈ conjSubgroup g V, (∀ z ∈ hOf M V h, ⁅u, z⁆ ∈ kOf V (hOf M V h)) ∧
      u ∈ Subgroup.centralizer (Tim79a.xOf V (hOf M V h) : Set G))
    (hPC : Pc M V = (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)))
    {x : G} (hx : x ∈ conjSubgroup g V) :
    ∃ H₁ : Subgroup G, H₁ ≤ hOf M V h ∧ kOf V (hOf M V h) ⊔ H₁ = hOf M V h ∧
      ∃ p₀ ∈ Pc M V ⊓ kOf V (hOf M V h), ∃ x₂ : G, x = p₀ * x₂ ∧
        x₂ ∈ Subgroup.centralizer (H₁ : Set G) := by
  classical
  have hR := hS.toRootHyp
  have hSh := hS.shape hU'
  obtain ⟨y₀, hy₀H, hPy₀, hVy₀, -⟩ := hR.exists_mem_conj_eq_of_eq_sup hSh.Pc_le hSh.hH
  obtain ⟨y, hyP_h, hyK⟩ := Sec45Shape.exists_mem_conjSubgroup_Pc_not_mem_kOf hR hSh
  have hyP : y ∈ conjSubgroup y₀ (Pc M V) := hPy₀.symm ▸ hyP_h
  have hyH : y ∈ hOf M V h := (conjSubgroup_le_of_le_of_mem hSh.Pc_le hy₀H) hyP
  have hyV : conjSubgroup y V ≠ V := by
    intro hc'
    have hyM : y ∈ M := by
      rw [← hR.toHyp.normalizer_eq]
      exact mem_normalizer_iff_conjSubgroup_eq.mpr hc'
    have hmem : y ∈ conjSubgroup y₀ (Pc M V) ⊓ M := ⟨hyP, hyM⟩
    rw [← hPy₀, hSh.conj_Pc_inf_M hR] at hmem
    exact hyK (Subgroup.mem_inf.mp hmem).2
  have hSh' : Sec45Shape M V (hOf M V h) y₀ := hSh.of_conjSubgroup_Pc_eq hPy₀.symm
  have hy₀V : conjSubgroup y₀ V ≠ V := fun hc' => ne_of_mem_sigmaSet hR hU' (hVy₀.trans hc')
  have hPC' : Pc M V = (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup y₀ V : Set G)) := by
    rw [← hVy₀]
    exact hPC
  have hCcK : Pc M V ⊓ Subgroup.centralizer (conjSubgroup y₀ V : Set G) =
      Pc M V ⊓ kOf V (hOf M V h) := hSh'.Pc_inf_centralizer_conj hR hy₀H hy₀V
  obtain ⟨hKF1, hKF2⟩ := hKF x hx
  have hxy : ⁅y, x⁆ ∈ kOf V (hOf M V h) := by
    rw [← commutatorElement_inv]
    exact (kOf V (hOf M V h)).inv_mem (hKF1 y hyH)
  have hxcent : x ∈ Subgroup.centralizer (conjSubgroup y₀ V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hcv : v ∈ conjSubgroup h V := by rw [hVy₀]; exact hv
    have hmem : ⁅v, x⁆ ∈ ⁅conjSubgroup h V, conjSubgroup g V⁆ :=
      Subgroup.commutator_mem_commutator hcv hx
    have hbot : ⁅conjSubgroup h V, conjSubgroup g V⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]; exact hc
    rw [hbot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)
  obtain ⟨n, hn, hyn⟩ :=
    Sec45Shape.exists_mem_inf_Pc_kOf_mul_mem_xOf (c := y₀) hR hSh' hy₀H hyP hyK hxy hxcent
  have hnP : n ∈ Pc M V := (Subgroup.mem_inf.mp hn).1
  have hnK : n ∈ kOf V (hOf M V h) := (Subgroup.mem_inf.mp hn).2
  have hH₁le : Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) ≤
      commMemSubgroup (hOf M V h) (Tim79a.xOf V (hOf M V h))
        (Tim79a.H_le_normalizer_xOf V (hOf M V h)) (n * x) :=
    Sec45Shape.le_commMemSubgroup_of_le_centralizer (h₀ := y₀) hR hSh' hnP hx
  have hy_mem : y ∈ commMemSubgroup (hOf M V h) (Tim79a.xOf V (hOf M V h))
      (Tim79a.H_le_normalizer_xOf V (hOf M V h)) (n * x) :=
    (mem_commMemSubgroup _ _ y).mpr ⟨hyH, hyn⟩
  have hsup : kOf V (hOf M V h) ⊔
      commMemSubgroup (hOf M V h) (Tim79a.xOf V (hOf M V h))
        (Tim79a.H_le_normalizer_xOf V (hOf M V h)) (n * x) = hOf M V h :=
    Sec45Shape.sup_kOf_commMemSubgroup_eq (c := y₀) hR hSh' hyV hy_mem hH₁le hPC' hCcK
  have hcomm : ∀ k ∈ commMemSubgroup (hOf M V h) (Tim79a.xOf V (hOf M V h))
      (Tim79a.H_le_normalizer_xOf V (hOf M V h)) (n * x) ⊓ kOf V (hOf M V h),
      k * (n * x) = (n * x) * k :=
    commutator_eq_one_of_mem_inf (c := y₀) hR hSh' hKF2 hx hnP hnK hPC' hCcK hyH hyV
      hy_mem
  obtain ⟨p₀, hp₀, x₂, hx₂, hcent⟩ :=
    exists_mem_Pc_inf_kOf_mul_mem_centralizer (H := hOf M V h) (h₀ := y₀) (g := g)
      (x := x) (n := n) (y := y) hR hSh' hPC' hCcK hnP hnK hx hH₁le hsup hcomm
  exact ⟨_, commMemSubgroup_le (hOf M V h) (Tim79a.xOf V (hOf M V h))
    (Tim79a.H_le_normalizer_xOf V (hOf M V h)) (n * x), hsup, p₀, hp₀, x₂, hx₂, hcent⟩

end CFSG.RankThree.GF2n.Tim81

end
