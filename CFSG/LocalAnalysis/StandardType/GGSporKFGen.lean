module

public import CFSG.LocalAnalysis.StandardType.GGSporKF1F4At
import CFSG.GroupTheory.BaerSuzuki.Helpers
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
import CFSG.GroupTheory.PrimeCorefreeQuasisimple
import CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter
import CFSG.GH74.GLS.Stage2.Bender.Thm1.IG109
import CFSG.LocalAnalysis.StandardType.GGSporKStepOne
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.CentralSylowComplement
import CFSG.CharacterTheory.Blocks.Defs
import CFSG.GH74.GLS.Defs
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der62
import CFSG.GH74.GLS.Stage2.Bender.Thm1.ExtraInv
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
import CFSG.GH74.GLS.Stage2.Final.Named
import CFSG.GH74.GLS.Stage2.Local.Concl
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly
open scoped commutatorElement

private theorem gkp_pCore_map_normal {X : Type*} [Group X] (p : ℕ) (H : Subgroup X) :
    ∀ h ∈ H, ∀ b ∈ (CFSG.pCore p H).map H.subtype,
      h * b * h⁻¹ ∈ (CFSG.pCore p H).map H.subtype := by
  intro h hh b hb
  obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
  refine Subgroup.mem_map.mpr ⟨⟨h, hh⟩ * b' * ⟨h, hh⟩⁻¹, ?_, rfl⟩
  exact (CFSG.pCore_normal (G := ↥H) (p := p)).conj_mem b' hb' ⟨h, hh⟩

private theorem gkp_pCore_map_isPGroup {X : Type*} [Group X] (p : ℕ) (H : Subgroup X) :
    IsPGroup p ((CFSG.pCore p H).map H.subtype) :=
  (CFSG.pCore_isPGroup (G := H) (p := p)).map H.subtype

private theorem gkp_c_mem_pCore_map {X : Type*} [Group X] {p : ℕ} (hp : p.Prime)
    {H : Subgroup X} {c : X} (hcH : c ∈ H) (hc : orderOf c = p)
    (hccent : ∀ g ∈ H, g * c = c * g) :
    c ∈ (CFSG.pCore p H).map H.subtype := by
  haveI : Fact p.Prime := ⟨hp⟩
  let cH : ↥H := ⟨c, hcH⟩
  have hord : orderOf cH = p := by
    rw [Subgroup.orderOf_mk c hcH, hc]
  have hcHcenter : cH ∈ Subgroup.center ↥H := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hccent g g.2)
  have hnorm : (Subgroup.zpowers cH).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcHcenter)
  have hpgrp : IsPGroup p (Subgroup.zpowers cH) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, hord, pow_one]
  have hle := CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup (G := ↥H) hnorm hpgrp
  exact Subgroup.mem_map.mpr ⟨cH, hle (Subgroup.mem_zpowers cH), rfl⟩

private theorem gkp_pCore_map_le_sylow {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {H S : Subgroup X} (hSp : IsPGroup p S)
    (hScard : Nat.card S = p ^ (Nat.card X).factorization p) (hSH : S ≤ H) :
    (CFSG.pCore p H).map H.subtype ≤ S := by
  haveI : Fact p.Prime := ⟨hp⟩
  let Sx : Sylow p X := Sylow.ofCard S hScard
  have hcoeeq : (Sx : Subgroup X) = S := Sylow.coe_ofCard S hScard
  have hPleH : (CFSG.pCore p H).map H.subtype ≤ H := Subgroup.map_subtype_le _
  let P' : Subgroup ↥H := CFSG.pCore p H
  let S' : Subgroup ↥H := S.subgroupOf H
  have hS'p : IsPGroup p S' := hSp.comap_subtype
  haveI : P'.Normal := CFSG.pCore_normal (G := ↥H) (p := p)
  have hP'p : IsPGroup p P' := CFSG.pCore_isPGroup (G := ↥H) (p := p)
  have hsup' : IsPGroup p ↥(S' ⊔ P') :=
    IsPGroup.to_sup_of_normal_right (p := p) (G := ↥H) (H := S') (K := P') hS'p hP'p
  have hmap : IsPGroup p ↥((CFSG.pCore p H).map H.subtype ⊔ S) := by
    have h := hsup'.map H.subtype
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hSH] at h
    rw [sup_comm] at h
    exact h
  have heq : (CFSG.pCore p H).map H.subtype ⊔ S = S :=
    Sx.is_maximal' hmap (by rw [hcoeeq]; exact le_sup_right)
  exact le_sup_left.trans (le_of_eq heq)

private theorem gkp_isExtraspecialPGroup {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {Q : Subgroup X} {c : X}
    (hQp : IsPGroup p Q) (hQexp : ∀ q ∈ Q, q ^ p = 1)
    (hQcomm : ⁅Q, Q⁆ = Subgroup.zpowers c)
    (hQcent : Q ⊓ Subgroup.centralizer (Q : Set X) = Subgroup.zpowers c)
    (hc : orderOf c = p) :
    CFSG.IsExtraspecialPGroup p ↥Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hzOf : CFSG.GH74.GLS.Bg.zOf Q = Subgroup.zpowers c := hQcent
  refine CFSG.GH74.GLS.Stage2.Bender.Thm1.isExtraspecial_of_extraG hp hQp hQexp
    (show CFSG.GH74.GLS.Stage2.Bender.Thm1.ExtraG p Q from ⟨?_, ?_⟩)
  · rw [hzOf, Nat.card_zpowers, hc]
  · rw [hQcomm, hzOf]

private theorem gkp_layer_eq_bot_of_noPComponent {X : Type} [Group X] [Finite X] {p : ℕ}
    {H : Subgroup X} (hP' : LargeEvenPPrimeCore p ↥H = ⊥)
    (hno : ∀ C : Subgroup X, ¬ LargeEvenPComponent p H C) :
    CFSG.layer ↥H = ⊥ := by
  have hnoComp : ∀ J : Subgroup X, ¬ CFSG.Assembly.IsComponentOf J H :=
    ggSporK_noComponent_of_noPComponent (W := X) p hP' hno
  rw [CFSG.layer.eq_sSup, eq_bot_iff]
  refine sSup_le fun K hK => ?_
  rw [le_bot_iff]
  by_contra hKne
  refine hnoComp (K.map H.subtype) ⟨Subgroup.map_subtype_le K, ?_, ?_⟩
  · have hsub : CFSG.Assembly.IsSubnormal K ⊤ :=
      CFSG.Assembly.IsSubnormal.of_mathlib hK.2
    have hmap := hsub.map H.subtype
    rwa [Subgroup.map_top, Subgroup.range_subtype] at hmap
  · have hqK : CFSG.Assembly.IsQuasisimple ↥K :=
      ⟨hK.1.1.commutator_eq_top, hK.1.2.1⟩
    exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
      (K.equivMapOfInjective H.subtype H.subtype_injective).symm hqK

private theorem gkp_c_ne_one {G : Type} [Group G] {p : ℕ} (hp : p.Prime) {c : G}
    (hc : orderOf c = p) : c ≠ 1 := by
  intro h1
  have : orderOf c = 1 := by rw [h1, orderOf_one]
  rw [hc] at this
  exact hp.ne_one this

private theorem gkp_commutator_le_zpowers {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {c : G} (hc : orderOf c = p) {S Q : Subgroup G}
    (hSp : IsPGroup p S) (hSc : S ≤ Subgroup.centralizer ({c} : Set G))
    (hQS : Q ≤ S) (hQn : S ≤ Subgroup.normalizer (Q : Set G))
    (hScard : Nat.card S = p ^ (Nat.card G).factorization p)
    (hQexp : ∀ q ∈ Q, q ^ p = 1) (hQcomm : ⁅Q, Q⁆ = Subgroup.zpowers c)
    (hQcent : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers c)
    (hirr : ∀ R : Subgroup G, Subgroup.zpowers c ≤ R → R ≤ Q →
      (∀ h ∈ Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.normalizer (Q : Set G),
        ∀ r ∈ R, h * r * h⁻¹ ∈ R) → R = Subgroup.zpowers c ∨ R = Q) :
    ⁅BMOpCent p c, Q⁆ ≤ Subgroup.zpowers c := by
  haveI : Fact p.Prime := ⟨hp⟩
  set H : Subgroup G := Subgroup.centralizer ({c} : Set G) with hH
  set P : Subgroup G := BMOpCent p c with hP
  have hPdef : P = (CFSG.pCore p H).map H.subtype := by rw [hP, hH, BMOpCent]
  have hcH : c ∈ H := by
    rw [hH]
    exact Subgroup.mem_centralizer_iff.mpr fun a ha => by
      rw [Set.mem_singleton_iff.mp ha]
  have hccent : ∀ g ∈ H, g * c = c * g := fun g hg =>
    (Subgroup.mem_centralizer_iff.mp hg c rfl).symm
  have hPH : P ≤ H := by rw [hPdef]; exact Subgroup.map_subtype_le _
  have hQH : Q ≤ H := hQS.trans hSc
  have hcP : c ∈ P := by
    rw [hPdef]; exact gkp_c_mem_pCore_map hp hcH hc hccent
  have hPp : IsPGroup p P := by rw [hPdef]; exact gkp_pCore_map_isPGroup p H
  have hPS : P ≤ S := by
    rw [hPdef]; exact gkp_pCore_map_le_sylow hp hSp hScard hSc
  have hPleNQ : P ≤ Subgroup.normalizer (Q : Set G) := hPS.trans hQn
  have hQQ : ⁅Q, Q⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem h₁ h₂) (Q.inv_mem h₁)) (Q.inv_mem h₂)
  have hQleQ : Subgroup.zpowers c ≤ Q := by rw [← hQcomm]; exact hQQ
  set W : Subgroup G := P ⊔ Q with hW
  have hPW : P ≤ W := by rw [hW]; exact le_sup_left
  have hQW : Q ≤ W := by rw [hW]; exact le_sup_right
  have hWH : W ≤ H := by rw [hW]; exact sup_le hPH hQH
  have hWS : W ≤ S := by rw [hW]; exact sup_le hPS hQS
  have hWp : IsPGroup p W := hSp.to_le hWS
  have hWleNQ : W ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hW]; exact sup_le hPleNQ Subgroup.le_normalizer
  have hcW : c ∈ W := hPW hcP
  let cW : W := ⟨c, hcW⟩
  have hcWcenter : cW ∈ Subgroup.center W := by
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hWH x.2) c rfl).symm
  let Zw : Subgroup W := Subgroup.zpowers cW
  have hZwn : Zw.Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcWcenter)
  have hZwmem : ∀ y : W, y ∈ Zw ↔ (y : G) ∈ Subgroup.zpowers c := by
    intro y
    rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, congrArg Subtype.val hk⟩,
      fun ⟨k, hk⟩ => ⟨k, Subtype.ext hk⟩⟩
  let Qw : Subgroup W := Q.subgroupOf W
  have hQwmem : ∀ y : W, y ∈ Qw ↔ (y : G) ∈ Q := fun y => Subgroup.mem_subgroupOf
  have hQwn : Qw.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQW).mpr hWleNQ
  let π : W →* W ⧸ Zw := QuotientGroup.mk' Zw
  have hπker : π.ker = Zw := QuotientGroup.ker_mk' Zw
  have hEp : IsPGroup p (W ⧸ Zw) := hWp.to_quotient Zw
  let N : Subgroup (W ⧸ Zw) := Qw.map π
  have hNn : N.Normal := hQwn.map π (QuotientGroup.mk'_surjective Zw)
  have hQnotle : ¬ Q ≤ Subgroup.zpowers c := by
    intro hle
    have hcomm : ⁅Q, Q⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro q' hq'
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hle hq)
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hle hq')
      rw [← zpow_add, ← zpow_add, add_comm]
    rw [hQcomm] at hcomm
    exact gkp_c_ne_one hp hc (Subgroup.zpowers_eq_bot.mp hcomm)
  have hNne : N ≠ ⊥ := by
    by_contra hbot
    have hle : Q ≤ Subgroup.zpowers c := by
      intro q hq
      have hqW : q ∈ W := hQW hq
      have hmem : π ⟨q, hqW⟩ ∈ N :=
        Subgroup.mem_map.mpr ⟨⟨q, hqW⟩, (hQwmem _).mpr hq, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      have hqZ : (⟨q, hqW⟩ : W) ∈ Zw := by
        rw [← hπker, MonoidHom.mem_ker]; exact hmem
      exact (hZwmem _).mp hqZ
    exact hQnotle hle
  haveI : N.Normal := hNn
  have hmeet : N ⊓ Subgroup.center (W ⧸ Zw) ≠ ⊥ :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter.inf_center_ne_bot
      hEp N hNne
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hmeet
  obtain ⟨haN, hacenter⟩ := Subgroup.mem_inf.mp a.2
  have ha1' : (a : W ⧸ Zw) ≠ 1 := fun h => ha1 (Subtype.ext h)
  obtain ⟨qw, hqw, hπqw⟩ := Subgroup.mem_map.mp haN
  have hcentral_le : ∀ y : W, π y ∈ Subgroup.center (W ⧸ Zw) →
      ∀ w : W, ⁅w, y⁆ ∈ Zw := by
    intro y hy w
    have hcomm : π w * π y = π y * π w := Subgroup.mem_center_iff.mp hy (π w)
    have h1 : π (w * y) = π (y * w) := by rw [map_mul, map_mul, hcomm]
    have h2 : π ((w * y) * (y * w)⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
    have hker : (w * y) * (y * w)⁻¹ ∈ π.ker := MonoidHom.mem_ker.mpr h2
    rw [hπker] at hker
    convert hker using 1
    rw [commutatorElement_def]; group
  have hconjW : ∀ (h : G) (hhH : h ∈ H) (hhN : h ∈ Subgroup.normalizer (Q : Set G))
      (z : W), ∃ z' : W, (z' : G) = h * (z : G) * h⁻¹ := by
    intro h hhH hhN z
    have hconjP : P.map (MulAut.conj h).toMonoidHom ≤ P := by
      rintro _ ⟨b, hb, rfl⟩
      rw [hPdef] at hb ⊢
      simpa [MulAut.conj_apply] using gkp_pCore_map_normal p H h hhH b hb
    have hconjQ : Q.map (MulAut.conj h).toMonoidHom ≤ Q := by
      rintro _ ⟨q, hq, rfl⟩
      simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp hhN q).mp hq
    have hconjW' : W.map (MulAut.conj h).toMonoidHom ≤ W := by
      rw [hW, Subgroup.map_sup]
      exact sup_le (hconjP.trans le_sup_left) (hconjQ.trans le_sup_right)
    exact ⟨⟨MulAut.conj h (z : G),
        hconjW' (Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom z.2)⟩,
      by simp [MulAut.conj_apply]⟩
  let Q₀ : Subgroup G := (Qw ⊓ Subgroup.comap π (Subgroup.center (W ⧸ Zw))).map W.subtype
  have hQwmap : Qw.map W.subtype = Q :=
    (Subgroup.subgroupOf_map_subtype Q W).trans (inf_eq_left.mpr hQW)
  have hQ₀leQ : Q₀ ≤ Q := (Subgroup.map_mono inf_le_left).trans (le_of_eq hQwmap)
  have hQ₀norm : ∀ h ∈ H ⊓ Subgroup.normalizer (Q : Set G), ∀ r ∈ Q₀, h * r * h⁻¹ ∈ Q₀ := by
    intro h hh r hr
    obtain ⟨hhH, hhN⟩ := Subgroup.mem_inf.mp hh
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hr
    obtain ⟨hyQw, hycenter⟩ := Subgroup.mem_inf.mp hy
    have hycenter' : π y ∈ Subgroup.center (W ⧸ Zw) := Subgroup.mem_comap.mp hycenter
    have hyQ : (y : G) ∈ Q := (hQwmem y).mp hyQw
    obtain ⟨y', hy'val⟩ := hconjW h hhH hhN y
    have hy'Qw : y' ∈ Qw := by
      rw [hQwmem, hy'val]
      exact (Subgroup.mem_normalizer_iff.mp hhN (y : G)).mp hyQ
    have hy'center : π y' ∈ Subgroup.center (W ⧸ Zw) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective Zw z
      obtain ⟨w'', hw''val⟩ :=
        hconjW h⁻¹ (H.inv_mem hhH) ((Subgroup.normalizer (Q : Set G)).inv_mem hhN) w
      have h1 : ((⁅w'', y⁆ : W) : G) ∈ Subgroup.zpowers c := by
        have := hcentral_le y hycenter' w''
        rwa [hZwmem] at this
      have hhc : h * c = c * h := (Subgroup.mem_centralizer_iff.mp hhH c rfl).symm
      have h2 : ((⁅w, y'⁆ : W) : G) = h * ((⁅w'', y⁆ : W) : G) * h⁻¹ := by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hw''val, hy'val]
        group
      have hmem : ((⁅w, y'⁆ : W) : G) ∈ Subgroup.zpowers c := by
        rw [h2]
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
        rw [← hk]
        have : h * c ^ k * h⁻¹ = c ^ k := by
          rw [(Commute.zpow_right (show Commute h c from hhc) k).eq]
          group
        rw [this]
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
      have hz : ⁅w, y'⁆ ∈ Zw := (hZwmem _).mpr hmem
      have hπ1 : π ⁅w, y'⁆ = 1 := by rw [← π.mem_ker, hπker]; exact hz
      have hc1 : π w * π y' = π y' * π w := by
        have := hπ1
        simp only [commutatorElement_def, map_mul, map_inv] at this
        rw [show π w * π y' * (π w)⁻¹ * (π y')⁻¹ = (π w * π y') * (π y' * π w)⁻¹ by group]
          at this
        exact mul_inv_eq_one.mp this
      exact hc1
    exact Subgroup.mem_map.mpr
      ⟨y', Subgroup.mem_inf.mpr ⟨hy'Qw, Subgroup.mem_comap.mpr hy'center⟩, hy'val⟩
  have hcQ₀ : Subgroup.zpowers c ≤ Q₀ := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine Subgroup.mem_map.mpr ⟨cW ^ k, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [hQwmem]
      exact hQleQ (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
    · rw [Subgroup.mem_comap, map_zpow,
        show π cW = 1 from by rw [← π.mem_ker, hπker]; exact Subgroup.mem_zpowers cW, one_zpow]
      exact Subgroup.one_mem _
    · rfl
  have hqQ₀ : (qw : G) ∈ Q₀ :=
    Subgroup.mem_map.mpr ⟨qw, Subgroup.mem_inf.mpr ⟨hqw,
      Subgroup.mem_comap.mpr (hπqw ▸ hacenter)⟩, rfl⟩
  have hqnotc : (qw : G) ∉ Subgroup.zpowers c := by
    intro hq
    have hqwZ : qw ∈ Zw := (hZwmem qw).mpr hq
    have h1 : π qw = 1 := by rw [← π.mem_ker, hπker]; exact hqwZ
    exact ha1' (by rw [← hπqw, h1])
  have hQ₀ne : Q₀ ≠ Subgroup.zpowers c := fun heq => hqnotc (heq ▸ hqQ₀)
  rcases hirr Q₀ hcQ₀ hQ₀leQ hQ₀norm with h | h
  · exact absurd h hQ₀ne
  · rw [Subgroup.commutator_le]
    intro p hp q hq
    have hq0 : q ∈ Q₀ := by rw [h]; exact hq
    obtain ⟨y, hy, hyq⟩ := Subgroup.mem_map.mp hq0
    obtain ⟨-, hycenter⟩ := Subgroup.mem_inf.mp hy
    have hycenter' : π y ∈ Subgroup.center (W ⧸ Zw) := Subgroup.mem_comap.mp hycenter
    have hpW : p ∈ W := hPW hp
    have hzw : (⁅(⟨p, hpW⟩ : W), y⁆ : W) ∈ Zw := hcentral_le y hycenter' ⟨p, hpW⟩
    have hg : ((⁅(⟨p, hpW⟩ : W), y⁆ : W) : G) ∈ Subgroup.zpowers c := (hZwmem _).mp hzw
    rw [commutatorElement_def]
    have heq : p * q * p⁻¹ * q⁻¹ = ((⁅(⟨p, hpW⟩ : W), y⁆ : W) : G) := by
      rw [← hyq]; rfl
    rw [heq]
    exact hg

private theorem gkp_centralizer_le_of_normal {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {c : G} (hc : orderOf c = p) {S Q : Subgroup G}
    (hSp : IsPGroup p S) (hScard : Nat.card S = p ^ (Nat.card G).factorization p)
    (hSc : S ≤ Subgroup.centralizer ({c} : Set G))
    (hQS : Q ≤ S) (hQn : S ≤ Subgroup.normalizer (Q : Set G))
    (hQcomm : ⁅Q, Q⁆ = Subgroup.zpowers c)
    (hQcent : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers c)
    (hCS : S ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers c)
    (hQnH : ∀ h ∈ Subgroup.centralizer ({c} : Set G), ∀ q ∈ Q, h * q * h⁻¹ ∈ Q)
    (hg1 : LargeEvenPPrimeCore p ↥(Subgroup.centralizer ({c} : Set G)) = ⊥) :
    Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer (Q : Set G) ≤ Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  set H : Subgroup G := Subgroup.centralizer ({c} : Set G) with hH
  set D : Subgroup G := H ⊓ Subgroup.centralizer (Q : Set G) with hD
  have hcH : c ∈ H := by
    rw [hH]
    exact Subgroup.mem_centralizer_iff.mpr fun a ha => by
      rw [Set.mem_singleton_iff.mp ha]
  have hQleH : Q ≤ H := hQS.trans hSc
  have hQQ : ⁅Q, Q⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem h₁ h₂) (Q.inv_mem h₁)) (Q.inv_mem h₂)
  have hQleQ : Subgroup.zpowers c ≤ Q := by rw [← hQcomm]; exact hQQ
  have hcQ : c ∈ Q := hQleQ (Subgroup.mem_zpowers c)
  have hndS : ¬ p ∣ S.index := by
    rw [← Sylow.coe_ofCard S hScard]
    exact (Sylow.ofCard S hScard).not_dvd_index
  have hSylS_H : CFSG.ABGLocalTools.IsSylowOf p S H := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨hSc, hSp,
      fun hd => hndS (hd.trans (Subgroup.relIndex_dvd_index_of_le hSc))⟩
  have hDH : D ≤ H := by rw [hD]; exact inf_le_left
  have hDnormal : ∀ h ∈ H, ∀ d ∈ D, h * d * h⁻¹ ∈ D := by
    intro h hh d hd
    rw [hD] at hd ⊢
    obtain ⟨hdH, hdC⟩ := Subgroup.mem_inf.mp hd
    refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hh hdH) (H.inv_mem hh), ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hdC ⊢
    intro q hq
    have hq' : h⁻¹ * q * h ∈ Q := by
      simpa using hQnH h⁻¹ (H.inv_mem hh) q hq
    calc q * (h * d * h⁻¹) = h * ((h⁻¹ * q * h) * d) * h⁻¹ := by group
      _ = h * (d * (h⁻¹ * q * h)) * h⁻¹ := by rw [hdC (h⁻¹ * q * h) hq']
      _ = (h * d * h⁻¹) * q := by group
  have hHnormD : H ≤ Subgroup.normalizer (D : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro d
    constructor
    · exact hDnormal h hh d
    · intro hd
      have h' := hDnormal h⁻¹ (H.inv_mem hh) (h * d * h⁻¹) hd
      rwa [show h⁻¹ * (h * d * h⁻¹) * h⁻¹⁻¹ = d by group] at h'
  have hDsyl : CFSG.ABGLocalTools.IsSylowOf p (S ⊓ D) D :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hSylS_H hDH hHnormD
  have hidxSD : ¬ p ∣ (S ⊓ D).relIndex D :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hDsyl).2.2
  have hSD : S ⊓ D = Subgroup.zpowers c := by
    rw [hD, hH, ← inf_assoc, inf_eq_left.mpr hSc, hCS]
  have hcent : ∀ x ∈ D, ∀ q ∈ Subgroup.zpowers c, x * q = q * x := by
    intro x hx q hq
    rw [hD] at hx
    obtain ⟨-, hxC⟩ := Subgroup.mem_inf.mp hx
    exact (Subgroup.mem_centralizer_iff.mp hxC q (hQleQ hq)).symm
  have hQleD : Subgroup.zpowers c ≤ D := by
    rw [hD]
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact H.zpow_mem hcH k
    · rw [Subgroup.mem_centralizer_iff]
      intro q hq
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (Commute.zpow_left (Subgroup.mem_centralizer_iff.mp (hSc (hQS hq)) c rfl) k).eq.symm
  have hQp : IsPGroup p (Subgroup.zpowers c) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, hc, pow_one]
  have hidx : ¬ p ∣ (Subgroup.zpowers c).relIndex D := by rw [← hSD]; exact hidxSD
  obtain ⟨O, hOX, hO, hinf, hdecomp⟩ :=
    CFSG.GroupTheory.exists_complement_of_central_sylow (p := p) hQleD hQp hcent hidx
  have hOnorm : ∀ h ∈ H, ∀ o ∈ O, h * o * h⁻¹ ∈ O := by
    intro h hh o ho
    have hoD : o ∈ D := hOX ho
    have hooD : h * o * h⁻¹ ∈ D := hDnormal h hh o hoD
    have hord : orderOf (h * o * h⁻¹) = orderOf o := by
      have h := MulEquiv.orderOf_eq (MulAut.conj h) o
      simpa [MulAut.conj_apply] using h
    rw [hO (h * o * h⁻¹) hooD, hord]
    exact (hO o hoD).mp ho
  have hOcop : Nat.Coprime p (Nat.card O) := by
    by_contra hnc
    have hdvd : p ∣ Nat.card O := by
      by_contra hd
      exact hnc ((hp.coprime_iff_not_dvd).mpr hd)
    obtain ⟨o, ho⟩ := exists_prime_orderOf_dvd_card' (G := ↥O) p hdvd
    have hnot := (hO (o : G) (hOX o.2)).mp o.2
    have ho' : orderOf (o : G) = p := by
      rw [Subgroup.orderOf_coe o, ho]
    rw [ho'] at hnot
    exact hnot dvd_rfl
  have hOcore : O.subgroupOf H ≤ CFSG.pPrimeCore p ↥H := by
    refine CFSG.GroupTheory.le_pPrimeCore_of_normal ?_ ?_
    · refine ⟨fun o ho h => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ho ⊢
      exact hOnorm h h.2 o ho
    · have he : Nat.card (O.subgroupOf H) = Nat.card O :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hOX.trans hDH)).toEquiv
      rw [he]; exact hOcop
  have hObot : O = ⊥ := by
    have hsub : O.subgroupOf H = ⊥ := by
      apply le_bot_iff.mp
      rw [← show CFSG.pPrimeCore p ↥H = ⊥ from hg1]
      exact hOcore
    apply le_bot_iff.mp
    intro o ho
    have hoH : o ∈ H := (hOX.trans hDH) ho
    have hmem : (⟨o, hoH⟩ : ↥H) ∈ O.subgroupOf H := ho
    rw [hsub, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  intro x hx
  obtain ⟨q, hq, o, ho, rfl⟩ := hdecomp x hx
  have ho1 : o = 1 := Subgroup.mem_bot.mp (hObot ▸ ho)
  rw [ho1, mul_one]
  exact hQleQ hq

theorem bmPCentralF1At_F4At_of_pLocal {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {c : G} (hc : orderOf c = p) {S Q : Subgroup G}
    (hSp : IsPGroup p S) (hScard : Nat.card S = p ^ (Nat.card G).factorization p)
    (hSc : S ≤ Subgroup.centralizer ({c} : Set G))
    (hQS : Q ≤ S) (hQn : S ≤ Subgroup.normalizer (Q : Set G))
    (hQexp : ∀ q ∈ Q, q ^ p = 1)
    (hQcomm : ⁅Q, Q⁆ = Subgroup.zpowers c)
    (hQcent : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers c)
    (hCS : S ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers c)
    (hirr : ∀ R : Subgroup G, Subgroup.zpowers c ≤ R → R ≤ Q →
      (∀ h ∈ Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.normalizer (Q : Set G),
        ∀ r ∈ R, h * r * h⁻¹ ∈ R) → R = Subgroup.zpowers c ∨ R = Q)
    (hg1 : LargeEvenPPrimeCore p ↥(Subgroup.centralizer ({c} : Set G)) = ⊥)
    (hno : ∀ C : Subgroup G, ¬ LargeEvenPComponent p (Subgroup.centralizer ({c} : Set G)) C) :
    BMPCentralF1At p c ∧ BMPCentralF4At p c := by
  haveI : Fact p.Prime := ⟨hp⟩
  set H : Subgroup G := Subgroup.centralizer ({c} : Set G) with hH
  set P : Subgroup G := BMOpCent p c with hP
  have hPdef : P = (CFSG.pCore p H).map H.subtype := by rw [hP, hH, BMOpCent]
  have hcH : c ∈ H := by
    rw [hH]
    exact Subgroup.mem_centralizer_iff.mpr fun a ha => by
      rw [Set.mem_singleton_iff.mp ha]
  have hccent : ∀ g ∈ H, g * c = c * g := fun g hg =>
    (Subgroup.mem_centralizer_iff.mp hg c rfl).symm
  have hPH : P ≤ H := by rw [hPdef]; exact Subgroup.map_subtype_le _
  have hQH : Q ≤ H := hQS.trans hSc
  have hcP : c ∈ P := by
    rw [hPdef]; exact gkp_c_mem_pCore_map hp hcH hc hccent
  have hPp : IsPGroup p P := by rw [hPdef]; exact gkp_pCore_map_isPGroup p H
  have hPS : P ≤ S := by
    rw [hPdef]; exact gkp_pCore_map_le_sylow hp hSp hScard hSc
  have hQp : IsPGroup p Q := hSp.to_le hQS
  have hQQ : ⁅Q, Q⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem h₁ h₂) (Q.inv_mem h₁)) (Q.inv_mem h₂)
  have hQleQ : Subgroup.zpowers c ≤ Q := by rw [← hQcomm]; exact hQQ
  have hPQ : ⁅P, Q⁆ ≤ Subgroup.zpowers c :=
    gkp_commutator_le_zpowers hp hc hSp hSc hQS hQn hScard hQexp hQcomm hQcent hirr
  have hQe : CFSG.IsExtraspecialPGroup p ↥Q :=
    gkp_isExtraspecialPGroup hp hQp hQexp hQcomm hQcent hc
  have hPleNQ : P ≤ Subgroup.normalizer (Q : Set G) := hPS.trans hQn
  have hQP : ⁅Q, P⁆ ≤ CFSG.GH74.GLS.Bg.zOf Q := by
    rw [show CFSG.GH74.GLS.Bg.zOf Q = Subgroup.zpowers c from hQcent]
    rw [Subgroup.commutator_comm]
    exact hPQ
  have hPleQ : P ≤ Q := by
    intro b hb
    obtain ⟨u, huQ, huC⟩ :=
      CFSG.GH74.GLS.Stage2.Bender.Thm1.exists_inner_of_extraspecial hp hQe hQexp hQP hPleNQ hb
    have hmem : u⁻¹ * b ∈ S ⊓ Subgroup.centralizer (Q : Set G) :=
      ⟨S.mul_mem (S.inv_mem (hQS huQ)) (hPS hb), huC⟩
    rw [hCS] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hb' : b = u * (u⁻¹ * b) := by group
    rw [hb', ← hk]
    exact Q.mul_mem huQ (hQleQ (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩))
  have hPne : P ≠ Subgroup.zpowers c := by
    intro hPeq
    have hlayer : CFSG.layer ↥H = ⊥ := gkp_layer_eq_bot_of_noPComponent hg1 hno
    have hchar : CFSG.IsCharacteristicP p ↥H :=
      CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot ↥H p
        (show CFSG.pPrimeCore p ↥H = ⊥ from hg1) hlayer
    let cH : ↥H := ⟨c, hcH⟩
    have hpc : CFSG.pCore p ↥H = Subgroup.zpowers cH := by
      apply Subgroup.map_injective H.subtype_injective
      have h1 : (CFSG.pCore p ↥H).map H.subtype = P := by rw [hPdef]
      have h2 : (Subgroup.zpowers cH).map H.subtype = Subgroup.zpowers c := by
        refine le_antisymm ?_ ?_
        · rw [Subgroup.map_le_iff_le_comap]
          intro z hz
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
          rw [Subgroup.mem_comap, map_zpow]
          exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
        · rw [Subgroup.zpowers_le]
          exact Subgroup.mem_map_of_mem H.subtype (Subgroup.mem_zpowers cH)
      rw [h1, hPeq, h2]
    have hchar' : Subgroup.centralizer (Subgroup.zpowers cH : Set ↥H) ≤ Subgroup.zpowers cH := by
      have h := hchar
      change Subgroup.centralizer (CFSG.pCore p ↥H : Set ↥H) ≤ CFSG.pCore p ↥H at h
      rwa [hpc] at h
    have htop : (⊤ : Subgroup ↥H) ≤ Subgroup.zpowers cH := by
      calc (⊤ : Subgroup ↥H)
          ≤ Subgroup.centralizer ((Subgroup.zpowers cH : Subgroup ↥H) : Set ↥H) := by
            intro x _
            rw [Subgroup.mem_centralizer_iff]
            intro z hz
            obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
            exact (Commute.zpow_right (show Commute x cH from Subtype.ext (hccent x x.2)) k).eq.symm
        _ ≤ Subgroup.zpowers cH := hchar'
    have hzptop : Subgroup.zpowers cH = ⊤ := top_le_iff.mp htop
    have hQle : Q ≤ Subgroup.zpowers c := by
      intro q hq
      have hqH : q ∈ H := hQH hq
      have hmem : (⟨q, hqH⟩ : ↥H) ∈ Subgroup.zpowers cH := by
        rw [hzptop]; exact Subgroup.mem_top _
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩
    have hbot : ⁅Subgroup.zpowers c, Subgroup.zpowers c⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_add, ← zpow_add, add_comm]
    have hle : Subgroup.zpowers c ≤ ⊥ := by
      rw [← hQcomm]
      exact (Subgroup.commutator_mono hQle hQle).trans (le_of_eq hbot)
    exact gkp_c_ne_one hp hc (Subgroup.zpowers_eq_bot.mp (le_bot_iff.mp hle))
  have hPQeq : P = Q := by
    have hPnorm : ∀ h ∈ H ⊓ Subgroup.normalizer (Q : Set G), ∀ r ∈ P, h * r * h⁻¹ ∈ P := by
      intro h hh r hr
      obtain ⟨hhH, -⟩ := Subgroup.mem_inf.mp hh
      rw [hPdef] at hr ⊢
      exact gkp_pCore_map_normal p H h hhH r hr
    rcases hirr P (Subgroup.zpowers_le.mpr hcP) hPleQ hPnorm with h | h
    · exact absurd h hPne
    · exact h
  have hQnH : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q := by
    intro h hh q hq
    have hqP : q ∈ P := by rw [hPQeq]; exact hq
    rw [← hPQeq]
    rw [hPdef] at hqP ⊢
    exact gkp_pCore_map_normal p H h hh q hqP
  have hcentQ : H ⊓ Subgroup.centralizer (Q : Set G) ≤ Q :=
    gkp_centralizer_le_of_normal hp hc hSp hScard hSc hQS hQn hQcomm hQcent hCS hQnH hg1
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hcP
    · show ⁅P, P⁆ = Subgroup.zpowers c
      rw [hPQeq, hQcomm]
    · show P ⊓ Subgroup.centralizer (P : Set G) = Subgroup.zpowers c
      rw [hPQeq, hQcent]
    · show H ⊓ Subgroup.centralizer (P : Set G) ≤ P
      rw [hPQeq]
      exact hcentQ
  · intro N hNH hNnorm hcN hNQ
    have hNQ' : N ≤ P := by rwa [← hP] at hNQ
    have hNQ'' : N ≤ Q := by rwa [hPQeq] at hNQ'
    have hNnorm' : ∀ h ∈ H ⊓ Subgroup.normalizer (Q : Set G), ∀ r ∈ N, h * r * h⁻¹ ∈ N :=
      fun h hh r hr => hNnorm h (Subgroup.mem_inf.mp hh).1 r hr
    rcases hirr N hcN hNQ'' hNnorm' with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h, ← hP, hPQeq])

end CFSG.StandardType.SporadicShape
