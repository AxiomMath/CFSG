module

public import CFSG.LocalAnalysis.WeakClosure81.W16QSetup
public import CFSG.LocalAnalysis.WeakClosure81.W16QL2
public import CFSG.LocalAnalysis.WeakClosure81.W16QExcL2A
public import CFSG.CGT.Timmesfeld75.L2Orbit
public import CFSG.LocalAnalysis.WeakClosure81.W16Seventeen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.CGT.Timmesfeld75 (IsL2Pair)
open Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

structure Exc1616 (M V₀ V U S H : Subgroup G)
    (φ : ↥(conjClosure V H) →* PSL(2, GaloisField 2 (E3.mQuot V (iSub16 V H)))) : Prop where
  cfg : Cfg1616 M V₀ V U S H
  surj : Function.Surjective φ
  ker : φ.ker = (iSub16 V H).subgroupOf (conjClosure V H)
  rank : mSub V₀ = E3.mQuot V (iSub16 V H)

structure Gen1616 (M V₀ V U S H : Subgroup G) (k : G) : Prop where
  cfg : Cfg1616 M V₀ V U S H
  mem : k ∈ conjClosure V H
  not_mem : k ∉ M
  gen : conjClosure V H ≤ V ⊔ conjSubgroup V k ⊔ iSub16 V H
  gen_inv : conjClosure V H ≤ V ⊔ conjSubgroup V k⁻¹ ⊔ iSub16 V H
  rank : mSub V₀ = E3.mQuot V (iSub16 V H)

namespace Exc1616

variable {M V₀ V U S H : Subgroup G}
  {φ : ↥(conjClosure V H) →* PSL(2, GaloisField 2 (E3.mQuot V (iSub16 V H)))}

private theorem w16q_le_sup_of_sup_conj_eq_top (e : Exc1616 M V₀ V U S H φ) {k : G}
    (hk : k ∈ conjClosure V H)
    (htop : ((V.subgroupOf (conjClosure V H)).map φ) ⊔
      CFSG.CGT.Timmesfeld75.conjSubgroup (φ ⟨k, hk⟩)⁻¹
        ((V.subgroupOf (conjClosure V H)).map φ) = ⊤) :
    conjClosure V H ≤ V ⊔ conjSubgroup V k ⊔ iSub16 V H := by
  have hVK : V ≤ conjClosure V H := le_conjClosure V H
  have hIK : iSub16 V H ≤ conjClosure V H := e.cfg.iSub16_le_conjClosure
  have hcK : conjSubgroup V k ≤ conjClosure V H := w16q_conjSubgroup_le_of_le hVK hk
  have hmap : ((V ⊔ conjSubgroup V k ⊔ iSub16 V H).subgroupOf (conjClosure V H)).map φ = ⊤ := by
    have hsub : (V ⊔ conjSubgroup V k ⊔ iSub16 V H).subgroupOf (conjClosure V H) =
        V.subgroupOf (conjClosure V H) ⊔ (conjSubgroup V k).subgroupOf (conjClosure V H) ⊔
          (iSub16 V H).subgroupOf (conjClosure V H) := by
      rw [Subgroup.subgroupOf_sup (sup_le hVK hcK) hIK,
        Subgroup.subgroupOf_sup hVK hcK]
    rw [hsub, Subgroup.map_sup, Subgroup.map_sup,
      w16q_map_conjSubgroup φ hVK hk,
      show (iSub16 V H).subgroupOf (conjClosure V H) = φ.ker from e.ker.symm,
      show φ.ker.map φ = ⊥ from Subgroup.map_ker_self φ]
    rw [htop]
    simp
  have hker : φ.ker ≤ (V ⊔ conjSubgroup V k ⊔ iSub16 V H).subgroupOf (conjClosure V H) := by
    rw [e.ker]
    exact Subgroup.subgroupOf_mono (conjClosure V H)
      (le_sup_right : iSub16 V H ≤ V ⊔ conjSubgroup V k ⊔ iSub16 V H)
  exact (Subgroup.subgroupOf_eq_top).1
    (Subgroup.map_injective_of_ker_le φ hker le_top
      (by rw [hmap, Subgroup.map_top_of_surjective φ e.surj]))

private theorem w16q_sup_conj_eq_top_of_not_mem_normalizer {X : Type} [Group X]
    {P : Subgroup X} {q : ℕ} (h : IsL2Pair X P q) {x : X}
    (hx : x ∉ normalizer (P : Set X)) :
    P ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup x P = ⊤ := by
  have hne : CFSG.CGT.Timmesfeld75.conjSubgroup x P ≠ P :=
    fun hconj => hx ((CFSG.CGT.Timmesfeld75.mem_normalizer_iff_conjSubgroup_eq).2 hconj)
  have htop := h.sup_conj_eq_top (a := 1) (b := x) (by
    rw [CFSG.CGT.Timmesfeld75.conjSubgroup_one]
    exact hne.symm)
  rwa [CFSG.CGT.Timmesfeld75.conjSubgroup_one] at htop

private theorem w16q_map_mem_normalizer_of_mem_M (e : Exc1616 M V₀ V U S H φ) {k : G}
    (hk : k ∈ conjClosure V H) (hkM : k ∈ M) :
    φ ⟨k, hk⟩ ∈ normalizer
      (((V.subgroupOf (conjClosure V H)).map φ : Subgroup _) : Set _) := by
  have hVK : V ≤ conjClosure V H := le_conjClosure V H
  have hconj : conjSubgroup V k = V :=
    conjSubgroup_eq_iff_mem_normalizer.2 (by rwa [e.cfg.cex.hyp.h6.normalizer_eq])
  have hmap := w16q_map_conjSubgroup φ hVK hk
  rw [hconj] at hmap
  have hinv : (φ ⟨k, hk⟩)⁻¹ ∈ normalizer
      (((V.subgroupOf (conjClosure V H)).map φ : Subgroup _) : Set _) :=
    (CFSG.CGT.Timmesfeld75.mem_normalizer_iff_conjSubgroup_eq).2 hmap.symm
  simpa using (normalizer _).inv_mem hinv

private theorem w16q_conj_mem_sup_of_mem_normalizer (e : Exc1616 M V₀ V U S H φ) {k : G}
    (hk : k ∈ conjClosure V H)
    (hkP : φ ⟨k, hk⟩ ∈ normalizer
      (((V.subgroupOf (conjClosure V H)).map φ : Subgroup _) : Set _))
    {v : G} (hv : v ∈ V) : k * v * k⁻¹ ∈ V ⊔ iSub16 V H := by
  have hvK : v ∈ conjClosure V H := (le_conjClosure V H) hv
  let vK : ↥(conjClosure V H) := ⟨v, hvK⟩
  have hvK' : vK ∈ V.subgroupOf (conjClosure V H) := hv
  have hmemP : φ (⟨k, hk⟩ * vK * ⟨k, hk⟩⁻¹) ∈
      (V.subgroupOf (conjClosure V H)).map φ := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 hkP _).1 (Subgroup.mem_map_of_mem φ hvK')
  have hmemComap : (⟨k, hk⟩ * vK * ⟨k, hk⟩⁻¹) ∈
      ((V.subgroupOf (conjClosure V H)).map φ).comap φ := hmemP
  rw [Subgroup.comap_map_eq, e.ker] at hmemComap
  have hsub : V.subgroupOf (conjClosure V H) ⊔
      (iSub16 V H).subgroupOf (conjClosure V H) =
      (V ⊔ iSub16 V H).subgroupOf (conjClosure V H) :=
    (Subgroup.subgroupOf_sup (le_conjClosure V H) e.cfg.iSub16_le_conjClosure).symm
  rw [hsub] at hmemComap
  exact hmemComap

private theorem w16q_conjSubgroup_inv_le_sup_of_mem_normalizer (e : Exc1616 M V₀ V U S H φ)
    {k : G} (hk : k ∈ conjClosure V H)
    (hkP : φ ⟨k, hk⟩ ∈ normalizer
      (((V.subgroupOf (conjClosure V H)).map φ : Subgroup _) : Set _)) :
    conjSubgroup V k⁻¹ ≤ V ⊔ iSub16 V H := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have hx' : k⁻¹ * x * k ∈ V := by simpa using hx
  have hmem := w16q_conj_mem_sup_of_mem_normalizer e hk hkP hx'
  rwa [show k * (k⁻¹ * x * k) * k⁻¹ = x by group] at hmem

theorem mQuot_ne_zero (e : Exc1616 M V₀ V U S H φ) : E3.mQuot V (iSub16 V H) ≠ 0 := by
  intro h0
  have hVp : IsPGroup 2 V := e.cfg.cex.hyp.isPGroup
  have hle : V ⊓ iSub16 V H ≤ V := inf_le_left
  have hEq : V ⊓ iSub16 V H = V :=
    (E3.mQuot_eq_zero_iff hVp hle).1 (by rw [w16q_mQuot_inf]; exact h0)
  have hVI : V ≤ iSub16 V H := hEq.ge.trans inf_le_right
  exact e.cfg.not_le (hVI.trans (Cex16.iSub16_le_pCoreOf e.cfg.cex e.cfg.min.fam16))

theorem isL2Pair_map (e : Exc1616 M V₀ V U S H φ) :
    IsL2Pair PSL(2, GaloisField 2 (E3.mQuot V (iSub16 V H)))
      ((V.subgroupOf (conjClosure V H)).map φ) (2 ^ E3.mQuot V (iSub16 V H)) := by
  have hVK : V ≤ conjClosure V H := le_conjClosure V H
  have hVp : IsPGroup 2 V := e.cfg.cex.hyp.isPGroup
  have hVKp : IsPGroup 2 (V.subgroupOf (conjClosure V H)) :=
    hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVK).symm
  refine isL2Pair_psl_of_card_eq (mQuot_ne_zero e) (hVKp.map φ) ?_
  have hcard : Nat.card ((V.subgroupOf (conjClosure V H)).map φ) *
      Nat.card ↥(φ.ker ⊓ V.subgroupOf (conjClosure V H)) =
      Nat.card (V.subgroupOf (conjClosure V H)) := by
    rw [← Subgroup.relIndex_ker (V.subgroupOf (conjClosure V H)) φ]
    exact Subgroup.relIndex_mul_card φ.ker (V.subgroupOf (conjClosure V H))
  have hkerinf : φ.ker ⊓ V.subgroupOf (conjClosure V H) =
      (V ⊓ iSub16 V H).subgroupOf (conjClosure V H) := by
    rw [e.ker]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    tauto
  have hcardVK : Nat.card (V.subgroupOf (conjClosure V H)) = Nat.card V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv
  have hcardI : Nat.card ↥(φ.ker ⊓ V.subgroupOf (conjClosure V H)) =
      Nat.card ↥(V ⊓ iSub16 V H) := by
    rw [hkerinf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((inf_le_right : V ⊓ iSub16 V H ≤ iSub16 V H).trans e.cfg.iSub16_le_conjClosure)).toEquiv
  have hcardV : Nat.card V = 2 ^ E3.mQuot V (V ⊓ iSub16 V H) * Nat.card ↥(V ⊓ iSub16 V H) :=
    E3.card_eq_two_pow_mul hVp inf_le_left
  rw [hcardI, hcardVK] at hcard
  have hcard' : Nat.card ((V.subgroupOf (conjClosure V H)).map φ) *
      Nat.card ↥(V ⊓ iSub16 V H) =
      2 ^ E3.mQuot V (V ⊓ iSub16 V H) * Nat.card ↥(V ⊓ iSub16 V H) := by
    rw [hcard]
    exact hcardV
  have hcancel : Nat.card ((V.subgroupOf (conjClosure V H)).map φ) =
      2 ^ E3.mQuot V (V ⊓ iSub16 V H) :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos hcard'
  rwa [w16q_mQuot_inf] at hcancel

theorem exists_gen (e : Exc1616 M V₀ V U S H φ) : ∃ k : G, Gen1616 M V₀ V U S H k := by
  have hL := e.isL2Pair_map
  obtain ⟨x, hx⟩ := exists_not_mem_normalizer_of_isL2Pair hL
  have hxinv : x⁻¹ ∉ normalizer
      (((V.subgroupOf (conjClosure V H)).map φ : Subgroup _) : Set _) :=
    fun h => hx (by simpa using (normalizer _).inv_mem h)
  obtain ⟨ξ, hξ⟩ := e.surj x
  refine ⟨(ξ : G), ⟨e.cfg, ξ.2, ?_, ?_, ?_, e.rank⟩⟩
  · intro hkM
    exact hx (hξ ▸ w16q_map_mem_normalizer_of_mem_M e ξ.2 hkM)
  · refine w16q_le_sup_of_sup_conj_eq_top e ξ.2 ?_
    rw [hξ]
    exact w16q_sup_conj_eq_top_of_not_mem_normalizer hL hxinv
  · refine w16q_le_sup_of_sup_conj_eq_top e ((conjClosure V H).inv_mem ξ.2) ?_
    have hφ : φ ⟨(ξ : G)⁻¹, (conjClosure V H).inv_mem ξ.2⟩ = x⁻¹ := by
      rw [show (⟨(ξ : G)⁻¹, (conjClosure V H).inv_mem ξ.2⟩ : ↥(conjClosure V H)) = ξ⁻¹ by rfl,
        map_inv, hξ]
    rw [hφ, inv_inv]
    exact w16q_sup_conj_eq_top_of_not_mem_normalizer hL hx

theorem isSylowIn_sup (e : Exc1616 M V₀ V U S H φ) :
    IsSylowIn 2 (V ⊔ iSub16 V H) (conjClosure V H) := by
  have hVK : V ≤ conjClosure V H := le_conjClosure V H
  have hIK : iSub16 V H ≤ conjClosure V H := e.cfg.iSub16_le_conjClosure
  have hVp : IsPGroup 2 V := e.cfg.cex.hyp.isPGroup
  have hIp : IsPGroup 2 (iSub16 V H) :=
    CFSG.Open.IsElemAbelian.isPGroup
      (Cex16.isElemAbelian_iSub16 e.cfg.one e.cfg.std e.cfg.cex e.cfg.min.fam16)
  have hVI : V ≤ normalizer (iSub16 V H : Set G) :=
    (e.cfg.cex.V_le_S.trans e.cfg.min.fam16.1).trans
      (le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H)
  refine ⟨sup_le hVK hIK, IsPGroup.to_sup_of_normal_right' hVp hIp hVI, ?_⟩
  have hPidx : ((V ⊔ iSub16 V H).subgroupOf (conjClosure V H)).index =
      ((V.subgroupOf (conjClosure V H)).map φ).index := by
    have hsub : (V ⊔ iSub16 V H).subgroupOf (conjClosure V H) =
        ((V.subgroupOf (conjClosure V H)).map φ).comap φ := by
      rw [Subgroup.comap_map_eq, e.ker]
      exact Subgroup.subgroupOf_sup hVK hIK
    rw [hsub, Subgroup.index_comap_of_surjective ((V.subgroupOf (conjClosure V H)).map φ) e.surj]
  change ¬ 2 ∣ ((V ⊔ iSub16 V H).subgroupOf (conjClosure V H)).index
  rw [hPidx]
  have hL := e.isL2Pair_map
  have hidx : ((V.subgroupOf (conjClosure V H)).map φ).index =
      (2 ^ E3.mQuot V (iSub16 V H)) ^ 2 - 1 := by
    have h1 : Nat.card ((V.subgroupOf (conjClosure V H)).map φ) *
        ((V.subgroupOf (conjClosure V H)).map φ).index =
        Nat.card (PSL(2, GaloisField 2 (E3.mQuot V (iSub16 V H)))) :=
      Subgroup.card_mul_index _
    rw [hL.card_eq, hL.card_eq_mul] at h1
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) h1
  rw [hidx]
  intro hdvd
  have h2sq : 2 ∣ (2 ^ E3.mQuot V (iSub16 V H)) ^ 2 := by
    rw [pow_two]
    exact dvd_mul_of_dvd_left (dvd_pow_self 2 (mQuot_ne_zero e)) _
  have hone : 2 ∣ 1 := by
    have h := Nat.dvd_sub h2sq hdvd
    rwa [Nat.sub_sub_self (Nat.one_le_pow 2 (2 ^ E3.mQuot V (iSub16 V H))
      (pow_pos (by norm_num) _))] at h
  exact Nat.prime_two.not_dvd_one hone

theorem mem_of_map_mem_normalizer (e : Exc1616 M V₀ V U S H φ) {k : G}
    (hk : k ∈ conjClosure V H)
    (hkP : φ ⟨k, hk⟩ ∈ normalizer
      (((V.subgroupOf (conjClosure V H)).map φ : Subgroup _) : Set _)) : k ∈ M := by
  have hle : conjSubgroup V k⁻¹ ≤ S :=
    (w16q_conjSubgroup_inv_le_sup_of_mem_normalizer e hk hkP).trans
      (sup_le e.cfg.cex.V_le_S
        ((Cex16.iSub16_le_pCoreOf e.cfg.cex e.cfg.min.fam16).trans
          (e.cfg.cex.pCoreOf_le_S e.cfg.one e.cfg.std e.cfg.min.fam16)))
  simpa using M.inv_mem (Cex16.mem_of_conj_le_S e.cfg.fifteen e.cfg.std e.cfg.cex hle)

theorem exists_sup_eq (e : Exc1616 M V₀ V U S H φ) {k₁ k₂ : G} (hk₁ : k₁ ∈ conjClosure V H)
    (hk₂ : k₂ ∈ conjClosure V H) (hM₁ : k₁ ∉ M) (hM₂ : k₂ ∉ M) :
    ∃ v ∈ V, conjSubgroup V k₂ ⊔ iSub16 V H = conjSubgroup V (k₁ * v) ⊔ iSub16 V H := by
  have hVK : V ≤ conjClosure V H := le_conjClosure V H
  have hL : IsL2Pair PSL(2, GaloisField 2 (E3.mQuot V (iSub16 V H)))
      ((V.subgroupOf (conjClosure V H)).map φ) (2 ^ E3.mQuot V (iSub16 V H)) :=
    e.isL2Pair_map
  have hx₁ : φ ⟨k₁, hk₁⟩ ∉ normalizer
      (((V.subgroupOf (conjClosure V H)).map φ : Subgroup _) : Set _) :=
    fun h => hM₁ (e.mem_of_map_mem_normalizer hk₁ h)
  have hx₂ : φ ⟨k₂, hk₂⟩ ∉ normalizer
      (((V.subgroupOf (conjClosure V H)).map φ : Subgroup _) : Set _) :=
    fun h => hM₂ (e.mem_of_map_mem_normalizer hk₂ h)
  have hx₁inv : (φ ⟨k₁, hk₁⟩)⁻¹ ∉ normalizer
      (((V.subgroupOf (conjClosure V H)).map φ : Subgroup _) : Set _) :=
    fun h => hx₁ (by simpa using (normalizer _).inv_mem h)
  have hx₂inv : (φ ⟨k₂, hk₂⟩)⁻¹ ∉ normalizer
      (((V.subgroupOf (conjClosure V H)).map φ : Subgroup _) : Set _) :=
    fun h => hx₂ (by simpa using (normalizer _).inv_mem h)
  have ha : CFSG.CGT.Timmesfeld75.conjSubgroup (φ ⟨k₁, hk₁⟩)⁻¹
      ((V.subgroupOf (conjClosure V H)).map φ) ≠
      (V.subgroupOf (conjClosure V H)).map φ :=
    fun h => hx₁inv ((CFSG.CGT.Timmesfeld75.mem_normalizer_iff_conjSubgroup_eq).2 h)
  have hb : CFSG.CGT.Timmesfeld75.conjSubgroup (φ ⟨k₂, hk₂⟩)⁻¹
      ((V.subgroupOf (conjClosure V H)).map φ) ≠
      (V.subgroupOf (conjClosure V H)).map φ :=
    fun h => hx₂inv ((CFSG.CGT.Timmesfeld75.mem_normalizer_iff_conjSubgroup_eq).2 h)
  obtain ⟨s, hsP, hs⟩ := hL.exists_mem_conj_eq ha hb
  obtain ⟨vK, hvK, hvφ⟩ := Subgroup.mem_map.1
    (((V.subgroupOf (conjClosure V H)).map φ).inv_mem hsP)
  have hAK : conjSubgroup V k₂ ⊔ iSub16 V H ≤ conjClosure V H :=
    sup_le (w16q_conjSubgroup_le_of_le hVK hk₂) e.cfg.iSub16_le_conjClosure
  have hBK : conjSubgroup V (k₁ * (vK : G)) ⊔ iSub16 V H ≤ conjClosure V H :=
    sup_le (w16q_conjSubgroup_le_of_le hVK ((conjClosure V H).mul_mem hk₁ vK.2))
      e.cfg.iSub16_le_conjClosure
  have hmapA : ((conjSubgroup V k₂ ⊔ iSub16 V H).subgroupOf (conjClosure V H)).map φ =
      CFSG.CGT.Timmesfeld75.conjSubgroup (φ ⟨k₂, hk₂⟩)⁻¹
        ((V.subgroupOf (conjClosure V H)).map φ) := by
    have hsup : (conjSubgroup V k₂ ⊔ iSub16 V H).subgroupOf (conjClosure V H) =
        (conjSubgroup V k₂).subgroupOf (conjClosure V H) ⊔
          (iSub16 V H).subgroupOf (conjClosure V H) :=
      Subgroup.subgroupOf_sup (w16q_conjSubgroup_le_of_le hVK hk₂)
        e.cfg.iSub16_le_conjClosure
    rw [hsup, Subgroup.map_sup, w16q_map_conjSubgroup φ hVK hk₂,
      show (iSub16 V H).subgroupOf (conjClosure V H) = φ.ker from e.ker.symm,
      show φ.ker.map φ = ⊥ from Subgroup.map_ker_self φ]
    simp
  have hmapB : ((conjSubgroup V (k₁ * (vK : G)) ⊔ iSub16 V H).subgroupOf
      (conjClosure V H)).map φ =
      CFSG.CGT.Timmesfeld75.conjSubgroup (φ ⟨k₂, hk₂⟩)⁻¹
        ((V.subgroupOf (conjClosure V H)).map φ) := by
    have hsup : (conjSubgroup V (k₁ * (vK : G)) ⊔ iSub16 V H).subgroupOf (conjClosure V H) =
        (conjSubgroup V (k₁ * (vK : G))).subgroupOf (conjClosure V H) ⊔
          (iSub16 V H).subgroupOf (conjClosure V H) :=
      Subgroup.subgroupOf_sup
        (w16q_conjSubgroup_le_of_le hVK ((conjClosure V H).mul_mem hk₁ vK.2))
        e.cfg.iSub16_le_conjClosure
    rw [hsup, Subgroup.map_sup,
      w16q_map_conjSubgroup φ hVK ((conjClosure V H).mul_mem hk₁ vK.2),
      show (iSub16 V H).subgroupOf (conjClosure V H) = φ.ker from e.ker.symm,
      show φ.ker.map φ = ⊥ from Subgroup.map_ker_self φ]
    simp only [sup_bot_eq]
    have hφ : φ ⟨k₁ * (vK : G), (conjClosure V H).mul_mem hk₁ vK.2⟩ =
        φ ⟨k₁, hk₁⟩ * s⁻¹ := by
      rw [show (⟨k₁ * (vK : G), (conjClosure V H).mul_mem hk₁ vK.2⟩ :
          ↥(conjClosure V H)) = ⟨k₁, hk₁⟩ * vK by rfl, map_mul, hvφ]
    rw [hφ, show (φ ⟨k₁, hk₁⟩ * s⁻¹)⁻¹ = s * (φ ⟨k₁, hk₁⟩)⁻¹ by group,
      ← CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    exact hs.symm
  have hkerA : φ.ker ≤ (conjSubgroup V k₂ ⊔ iSub16 V H).subgroupOf (conjClosure V H) := by
    rw [e.ker]
    exact Subgroup.subgroupOf_mono (conjClosure V H)
      (le_sup_right : iSub16 V H ≤ conjSubgroup V k₂ ⊔ iSub16 V H)
  have hkerB : φ.ker ≤ (conjSubgroup V (k₁ * (vK : G)) ⊔ iSub16 V H).subgroupOf
      (conjClosure V H) := by
    rw [e.ker]
    exact Subgroup.subgroupOf_mono (conjClosure V H)
      (le_sup_right : iSub16 V H ≤ conjSubgroup V (k₁ * (vK : G)) ⊔ iSub16 V H)
  have hsubeq : (conjSubgroup V k₂ ⊔ iSub16 V H).subgroupOf (conjClosure V H) =
      (conjSubgroup V (k₁ * (vK : G)) ⊔ iSub16 V H).subgroupOf (conjClosure V H) :=
    Subgroup.map_injective_of_ker_le φ hkerA hkerB (by rw [hmapA, hmapB])
  have hAB : conjSubgroup V k₂ ⊔ iSub16 V H =
      conjSubgroup V (k₁ * (vK : G)) ⊔ iSub16 V H := by
    have h := (Subgroup.subgroupOf_inj).1 hsubeq
    rwa [inf_eq_left.2 hAK, inf_eq_left.2 hBK] at h
  exact ⟨(vK : G), hvK, hAB⟩

end Exc1616

namespace Gen1616

variable {M V₀ V U S H : Subgroup G} {k : G}

theorem inv (g : Gen1616 M V₀ V U S H k) : Gen1616 M V₀ V U S H k⁻¹ :=
  ⟨g.cfg, (conjClosure V H).inv_mem g.mem, fun h => g.not_mem (by simpa using M.inv_mem h),
    g.gen_inv, by simpa using g.gen, g.rank⟩

end Gen1616

end CFSG.LocalAnalysis.WeakClosure81

end
