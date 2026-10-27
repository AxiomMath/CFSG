module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Hyp
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenSmallCls
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.Main
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenW3

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}


theorem nine3_bar (h : Nine3T79Setup V T A K S X p g x)
    (hCore : OddTranspositionCoreInputSCCls) (hList : OddTranspListBundleCls)
    (h772 : SevenSevenTwoInput (nine3G1 V K g)) (hIn : OrthReflParabolic) :
    ∃ (Z : Type) (_ : Group Z) (Ψ : ↥(nineH0 V K g) →* Z),
      Function.Surjective Ψ ∧ Nine3QuotHyp (nineH0 V K g) Ψ ∧ CFSG.pCore 2 Z = ⊥ ∧
      SevenElevenSmallAltCls Z ((V.subgroupOf (nineH0 V K g)).map Ψ) := by
  classical
  let q : ↥(nineH0 V K g) →* nine3G1 V K g :=
    QuotientGroup.mk' (fusionOddCore ↥(nineH0 V K g))
  let K₀ : Subgroup (nine3G1 V K g) :=
    kSub (nine3BarV V K g) (⊤ : Subgroup (nine3G1 V K g)) (nine3BarE V K g)
  have hK : K₀ = ⊤ := nine3_kSub_barV h
  let φ : ↥K₀ →* (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) :=
    QuotientGroup.mk' (CFSG.pCore 2 ↥K₀)
  let Ψ0 : ↥(nineH0 V K g) →* ↥K₀ :=
    q.codRestrict K₀ (fun y => by rw [hK]; exact Subgroup.mem_top _)
  let Ψ : ↥(nineH0 V K g) →* (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) := φ.comp Ψ0
  have hpCoreK : pCoreOf 2 K₀ = CFSG.pCore 2 (nine3G1 V K g) := by
    rw [hK, CFSG.Quasithin.B6.pCoreOf_top 2 (nine3G1 V K g)]
  have hmap_le : (CFSG.pCore 2 ↥(nineH0 V K g)).map q ≤
      CFSG.pCore 2 (nine3G1 V K g) := by
    have hNnormal : ((CFSG.pCore 2 ↥(nineH0 V K g)).map q).Normal :=
      Subgroup.Normal.map (inferInstance : (CFSG.pCore 2 ↥(nineH0 V K g)).Normal) q
        (QuotientGroup.mk'_surjective _)
    have hNp : IsPGroup 2 ((CFSG.pCore 2 ↥(nineH0 V K g)).map q) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(nineH0 V K g))).map q
    have hnorm : (⊤ : Subgroup (nine3G1 V K g)) ≤
        Subgroup.normalizer ((CFSG.pCore 2 ↥(nineH0 V K g)).map q :
          Set (nine3G1 V K g)) :=
      le_of_eq (Subgroup.normalizer_eq_top_iff.mpr hNnormal).symm
    have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2)
      (N := (CFSG.pCore 2 ↥(nineH0 V K g)).map q)
      (H := (⊤ : Subgroup (nine3G1 V K g))) le_top hnorm hNp
    rwa [CFSG.Quasithin.B6.pCoreOf_top 2 (nine3G1 V K g)] at hle
  have hpcore_le : ∀ k : ↥(nineH0 V K g), (k : G) ∈ pCoreOf 2 (nineH0 V K g) →
      Ψ k = 1 := by
    intro k hk
    have hk' : k ∈ CFSG.pCore 2 ↥(nineH0 V K g) := by
      have h := hk
      rw [show pCoreOf 2 (nineH0 V K g) =
        (CFSG.pCore 2 ↥(nineH0 V K g)).map (nineH0 V K g).subtype from rfl] at h
      exact (Subgroup.mem_map_iff_mem (nineH0 V K g).subtype_injective).mp h
    have hqk : (Ψ0 k : nine3G1 V K g) ∈ pCoreOf 2 K₀ := by
      have h1 : q k ∈ CFSG.pCore 2 (nine3G1 V K g) :=
        hmap_le (Subgroup.mem_map_of_mem q hk')
      rw [hpCoreK]
      exact h1
    show φ (Ψ0 k) = 1
    exact ((isBarMap_mk_pCore K₀).ker_iff (Ψ0 k)).mpr hqk
  have hsub : (V.subgroupOf (nineH0 V K g)).map Ψ0 =
      (nine3BarV V K g).subgroupOf K₀ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, hxq⟩
      exact ⟨x, hx, Subtype.ext hxq⟩
  have hmap : (V.subgroupOf (nineH0 V K g)).map Ψ =
      barSub K₀ φ (nine3BarV V K g) := by
    rw [barSub]
    show (V.subgroupOf (nineH0 V K g)).map (φ.comp Ψ0) =
      ((nine3BarV V K g).subgroupOf K₀).map φ
    rw [← Subgroup.map_map, hsub]
  have hVdcal : V ∈ nine3Dcal V (nineH0 V K g) :=
    ⟨1, (nineH0 V K g).one_mem, (CFSG.Quasithin.conjSubgroup_one V).symm⟩
  have hker_inf : Ψ.ker ⊓ V.subgroupOf (nineH0 V K g) =
      (pCoreOf 2 (nineH0 V K g) ⊓ V).subgroupOf (nineH0 V K g) := by
    ext x
    constructor
    · intro hx
      have hxV : (x : G) ∈ V := hx.2
      have hqk : q x ∈ CFSG.pCore 2 (nine3G1 V K g) := by
        have h1 : (Ψ0 x : nine3G1 V K g) ∈ pCoreOf 2 K₀ :=
          ((isBarMap_mk_pCore K₀).ker_iff (Ψ0 x)).mp (MonoidHom.mem_ker.mp hx.1)
        have h2 : (Ψ0 x : nine3G1 V K g) ∈ CFSG.pCore 2 (nine3G1 V K g) := by
          rwa [hpCoreK] at h1
        exact h2
      have hD2 : IsPGroup 2 (Subgroup.zpowers (x : G)) := by
        refine IsPGroup.of_card_dvd_pow (n := 1) ?_
        rw [Nat.card_zpowers, Subgroup.orderOf_coe]
        simpa using orderOf_dvd_of_pow_eq_one (h.hc.core.hyp7.1.2 (x : G) hxV)
      have hDle : (Subgroup.zpowers (x : G)).subgroupOf (nineH0 V K g) ≤
          (CFSG.pCore 2 (nine3G1 V K g)).comap q := by
        intro y hy
        rw [Subgroup.mem_subgroupOf] at hy
        rw [Subgroup.mem_comap]
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy
        have hyk : y = x ^ m := Subtype.ext (by simpa using hm.symm)
        rw [hyk, map_zpow]
        exact (CFSG.pCore 2 (nine3G1 V K g)).zpow_mem hqk m
      have hle := nine3_le_pCore_of_le_comap h
        (Subgroup.zpowers_le.mpr ((nine3_V_le_H0 h.hc) hxV)) hD2 hDle
      exact ⟨hle (Subgroup.mem_zpowers (x : G)), hxV⟩
    · intro hx
      exact ⟨hpcore_le x hx.1, hx.2⟩
  have hcard : Nat.card ((V.subgroupOf (nineH0 V K g)).map Ψ) = 2 := by
    rw [← Subgroup.relIndex_ker Ψ (K := V.subgroupOf (nineH0 V K g))]
    rw [← Subgroup.inf_relIndex_right (H := Ψ.ker)
      (K := V.subgroupOf (nineH0 V K g)), hker_inf]
    rw [Subgroup.relIndex_subgroupOf (nine3_V_le_H0 h.hc), Subgroup.inf_relIndex_right]
    exact (nine3_dcal_not_le_pCore h hVdcal).2
  have hS : Nat.card (barSub K₀ φ (nine3BarV V K g)) = 2 := by
    rw [← hmap]
    exact hcard
  refine ⟨↥K₀ ⧸ CFSG.pCore 2 ↥K₀, inferInstance, Ψ, ?_, ?_, ?_, ?_⟩
  · have hΨ0 : Function.Surjective Ψ0 := by
      intro y
      obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective (fusionOddCore ↥(nineH0 V K g))
        (y : nine3G1 V K g)
      refine ⟨z, ?_⟩
      apply Subtype.ext
      change q z = (y : nine3G1 V K g)
      exact hz
    exact (isBarMap_mk_pCore K₀).surjective.comp hΨ0
  · refine ⟨hpcore_le, ?_⟩
    intro k hk n hord
    have hqk : q k ∈ CFSG.pCore 2 (nine3G1 V K g) := by
      have h1 : (Ψ0 k : nine3G1 V K g) ∈ pCoreOf 2 K₀ :=
        ((isBarMap_mk_pCore K₀).ker_iff (Ψ0 k)).mp hk
      have h2 : (Ψ0 k : nine3G1 V K g) ∈ CFSG.pCore 2 (nine3G1 V K g) := by
        rwa [hpCoreK] at h1
      exact h2
    have hD2 : IsPGroup 2 (Subgroup.zpowers (k : G)) := by
      refine IsPGroup.of_card_dvd_pow (n := n) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hord]
    have hDle : (Subgroup.zpowers (k : G)).subgroupOf (nineH0 V K g) ≤
        (CFSG.pCore 2 (nine3G1 V K g)).comap q := by
      intro y hy
      rw [Subgroup.mem_subgroupOf] at hy
      rw [Subgroup.mem_comap]
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hyk : y = k ^ m := Subtype.ext (by simpa using hm.symm)
      rw [hyk, map_zpow]
      exact (CFSG.pCore 2 (nine3G1 V K g)).zpow_mem hqk m
    have hle := nine3_le_pCore_of_le_comap h (Subgroup.zpowers_le.mpr k.2) hD2 hDle
    exact hle (Subgroup.mem_zpowers (k : G))
  · exact pCore_eq_bot_of_isBarMap (isBarMap_mk_pCore K₀)
  · have hcls : SevenElevenSmallAltCls (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)
        (barSub K₀ φ (nine3BarV V K g)) :=
      (seven_eleven_small_cls (G := nine3G1 V K g) hCore hList
        (OddCentral.sevenSevenOddCentral (nine3G1 V K g)) h772 hIn (nine3_hyp711 h)
        (isBarMap_mk_pCore K₀) hS).2
    rw [hmap]
    exact hcls

end CFSG.LocalAnalysis.WeakClosure81
