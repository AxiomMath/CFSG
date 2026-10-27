module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs812
public import CFSG.GroupTheory.ConjActionModPCore
import CFSG.GroupTheory.PCore.InfPCoreOf
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.GroupTheory.PRankCoprimeQuotient
import CFSG.GroupTheory.PrimeField.SteinbergBNPowerComparison
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.Quasithin.Vol2.Ch10SecB6Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.Ctx812

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Ctx812E

theorem mem_AA_of_pow_three_eq_one (c : Ctx812E G) (d : SylowThreeData G)
    (hdM : d.M = c.S.M) (hdL : d.L = c.L) {x : G} (hxM : x ∈ c.S.M)
    (hxS : x ∈ Subgroup.normalizer (d.S : Set G))
    (hxL : ∀ i, x ∈ Subgroup.normalizer (d.Lf i : Set G)) (hx3 : x ^ 3 = 1) : x ∈ d.AA := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hxnot
  have hx1 : x ≠ 1 := fun h => hxnot (h ▸ d.AA.one_mem)
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hx3' : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  have hcardR : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hord]
  have hdisj : Disjoint d.AA (Subgroup.zpowers x) := by
    rw [Subgroup.disjoint_def]
    intro y hyA hyR
    haveI : Fact (Nat.Prime (Nat.card (Subgroup.zpowers x))) := ⟨by rw [hcardR]; norm_num⟩
    have hH : (d.AA ⊓ Subgroup.zpowers x).subgroupOf (Subgroup.zpowers x) = ⊥ := by
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card
        ((d.AA ⊓ Subgroup.zpowers x).subgroupOf (Subgroup.zpowers x)) with h | h
      · exact h
      · exfalso
        rw [Subgroup.subgroupOf_eq_top] at h
        exact hxnot (h (Subgroup.mem_zpowers x)).1
    have hmem : (⟨y, hyR⟩ : Subgroup.zpowers x) ∈
        (d.AA ⊓ Subgroup.zpowers x).subgroupOf (Subgroup.zpowers x) :=
      Subgroup.mem_subgroupOf.mpr ⟨hyA, hyR⟩
    rw [hH] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  have hcomm : ∀ a ∈ d.AA, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    have hax : x * a = a * x := d.threeElement_centralizes_AA hx3' hxS hxL a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((show Commute a x from hax.symm).zpow_right k).eq
  have hAA_le_M : d.AA ≤ c.S.M := by
    rw [← hdM]
    have hLM : d.L ≤ d.M := by
      rw [d.hL]
      exact sup_le (sup_le (d.hLM 0) (d.hLM 1)) (d.hLM 2)
    exact d.AA_le_S.trans (d.hS.le.trans hLM)
  have hAA_rank : CFSG.Open.pRank 3 d.AA = 3 := by
    refine le_antisymm ?_ (CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl
      d.isElemAbelian_AA (k := 3) (by rw [d.card_AA]; norm_num))
    have h := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hAA_le_M
    rwa [c.pRank_three_M] at h
  have hR_rank : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers x) :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl
      (CFSG.Open.isElemAbelian_zpowers hx3) (k := 1) (by rw [hcardR]; norm_num)
  have hupper : CFSG.Open.pRank 3 (d.AA ⊔ Subgroup.zpowers x) ≤ 3 := by
    have h := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num)
      (H := d.AA ⊔ Subgroup.zpowers x) (K := c.S.M)
      (sup_le hAA_le_M (Subgroup.zpowers_le.mpr hxM))
    rwa [c.pRank_three_M] at h
  have hsum := CFSG.Quasithin.Vol2.Ch10.SecB.pRank_add_le_pRank_sup' (p := 3) Nat.prime_three
    (A := d.AA) (B := Subgroup.zpowers x) hcomm (disjoint_iff.mp hdisj)
  omega

end Ctx812E

namespace SylowThreeData

variable (d : SylowThreeData G)

theorem commutator_Lf_H_le {i j : Fin 3} (hij : i ≠ j) :
    ⁅d.Lf i, d.H j⁆ ≤ CFSG.Open.pCoreOf 2 (d.Lf i) := by
  have hHnorm : d.H j ≤ Subgroup.normalizer (d.Lf i : Set G) :=
    (d.H_le_Lf j).trans (d.hLnorm i j)
  have h1 : ⁅d.Lf i, d.H j⁆ ≤ d.Lf i :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hHnorm
  have h2 : ⁅d.Lf i, d.H j⁆ ≤ CFSG.Open.pCoreOf 2 d.M :=
    (Subgroup.commutator_mono le_rfl (d.H_le_Lf j)).trans (d.hcomm i j hij)
  exact (le_inf h1 h2).trans (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 (d.hLM i))

theorem conjModPCore_H_eq_one {P₀ : Subgroup G}
    (hPn : ∀ k, P₀ ≤ Subgroup.normalizer (d.Lf k : Set G))
    (hHP : ∀ k, d.H k ≤ P₀) {i j : Fin 3} (hij : i ≠ j) {h : G} (hh : h ∈ d.H j) :
    CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hPn i) ⟨h, hHP j hh⟩ = 1 := by
  have hRle : d.H j ≤ ((CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hPn i)).ker.map
      P₀.subtype) :=
    (CFSG.GroupTheory.le_map_ker_conjModPCore_iff_commutator 2 (d.Lf i) P₀ (d.H j) (hPn i)
      (hHP j)).mpr (commutator_Lf_H_le d hij)
  obtain ⟨a, ha, hay⟩ := hRle hh
  rw [show (⟨h, hHP j hh⟩ : ↥P₀) = a from Subtype.ext hay.symm]
  exact MonoidHom.mem_ker.mp ha

theorem eq_one_of_mem_H_of_forall_commutator_mem (i : Fin 3) {h : G} (hh : h ∈ d.H i)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center (↥(d.Lf i) ⧸ CFSG.Open.pCore 2 ↥(d.Lf i))))
    (hfix : ∀ x ∈ d.Lf i, h * x * h⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 (d.Lf i)) : h = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : h ∈ d.Lf i := d.H_le_Lf i hh
  set Pc : Subgroup ↥(d.Lf i) := CFSG.Open.pCore 2 ↥(d.Lf i) with hPc
  let X : Type := ↥(d.Lf i) ⧸ Pc
  letI : Group X := inferInstance
  letI : Finite X := inferInstance
  let hbar : X := QuotientGroup.mk (s := Pc) ⟨h, hL⟩
  have hcent : hbar ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Pc w
    have hmem : (⟨h, hL⟩ * y * ⟨h, hL⟩⁻¹ * y⁻¹ : ↥(d.Lf i)) ∈ Pc := by
      rw [← Subgroup.mem_map_iff_mem (d.Lf i).subtype_injective]
      simpa [CFSG.Open.pCoreOf] using hfix (y : G) y.2
    have hclass : (↑(⟨h, hL⟩ * y * ⟨h, hL⟩⁻¹ * y⁻¹) : X) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem
    have key : hbar * (↑y : X) * hbar⁻¹ = ↑y := by
      have hprod : hbar * (↑y : X) * hbar⁻¹ =
          ((⟨h, hL⟩ * y * ⟨h, hL⟩⁻¹ : ↥(d.Lf i)) : X) := by
        show (QuotientGroup.mk (s := Pc) ⟨h, hL⟩) *
            (↑y : ↥(d.Lf i) ⧸ CFSG.Open.pCore 2 ↥(d.Lf i)) *
            (QuotientGroup.mk (s := Pc) ⟨h, hL⟩)⁻¹ = _
        simp only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
      have hdiv : ((⟨h, hL⟩ * y * ⟨h, hL⟩⁻¹ : ↥(d.Lf i)) : X) = (↑y : X) := by
        rw [QuotientGroup.eq_iff_div_mem, ← Subgroup.mem_map_iff_mem (d.Lf i).subtype_injective]
        simpa [CFSG.Open.pCoreOf, div_eq_mul_inv] using hfix (y : G) y.2
      rw [hprod, hdiv]
    calc (↑y : X) * hbar = (hbar * (↑y : X) * hbar⁻¹) * hbar := by rw [key]
      _ = hbar * (↑y : X) := by group
  have hH3 : IsPGroup 3 (d.H i) := IsPGroup.to_le d.hS.isPGroup (d.H_le_S i)
  obtain ⟨n, hn⟩ := hH3.exists_card_eq
  have hdvdH : orderOf h ∣ 3 ^ n := hn ▸ Subgroup.orderOf_dvd_natCard (d.H i) hh
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvdH
  have hdvd_bar : orderOf hbar ∣ 3 ^ k := by
    rw [← hk]
    have h1 : hbar = (QuotientGroup.mk' Pc) ⟨h, hL⟩ := rfl
    rw [h1]
    exact Nat.dvd_trans (orderOf_map_dvd (QuotientGroup.mk' Pc) ⟨h, hL⟩)
      (by rw [Subgroup.orderOf_mk h hL])
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd_bar
  have hbar1 : hbar = 1 := by
    refine CFSG.GroupTheory.PrimeField.eq_one_of_pow_eq_one_of_coprime (m := 3 ^ m) hcent ?_ ?_
    · exact (Nat.coprime_comm.mpr
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ)).pow_right m
    · rw [← hm]
      exact pow_orderOf_eq_one hbar
  have hpk : (⟨h, hL⟩ : ↥(d.Lf i)) ∈ Pc :=
    (QuotientGroup.eq_one_iff (⟨h, hL⟩ : ↥(d.Lf i))).mp hbar1
  have hmem2 : h ∈ CFSG.Open.pCoreOf 2 (d.Lf i) := Subgroup.mem_map_of_mem _ hpk
  have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (d.Lf i)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hdisj := IsPGroup.disjoint_of_ne 3 2 (by norm_num) (d.H i)
    (CFSG.Open.pCoreOf 2 (d.Lf i)) hH3 hO2
  have hmem : h ∈ d.H i ⊓ CFSG.Open.pCoreOf 2 (d.Lf i) := ⟨hh, hmem2⟩
  rw [hdisj.eq_bot] at hmem
  exact Subgroup.mem_bot.mp hmem

end SylowThreeData

namespace Ctx812E

private theorem exists_mem_H_mul_pow_three_eq_one (c : Ctx812E G) (hK8 : OuterThreeSplit)
    (d : SylowThreeData G) (hdM : d.M = c.S.M)
    (hcomp : ∀ i, CFSG.Yardstones.Mf4cdcdf2e013.Asc83CComponent c.S.M (d.Lf i))
    {P₀ : Subgroup G} (hP03 : IsPGroup 3 P₀) (hP0M : P₀ ≤ d.M)
    (hPn : ∀ i, P₀ ≤ Subgroup.normalizer (d.Lf i : Set G))
    (hHP : ∀ i, d.H i ≤ P₀) (i : Fin 3) {x : G} (hxP0 : x ∈ P₀)
    (hx3S : x ^ 3 ∈ d.S) :
    ∃ h : ↥(d.H i), ((CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hPn i))
        ⟨(h : G), hHP i h.2⟩ *
      (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hPn i)) ⟨x, hxP0⟩) ^ 3 = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hN, hQ⟩ := (hcomp i).2.2.2
  let X : Type := ↥(d.Lf i) ⧸ CFSG.Open.pCore 2 ↥(d.Lf i)
  letI : Group X := inferInstance
  letI : Finite X := inferInstance
  have hQX : CFSG.Open.IsQuasisimple X := hQ
  haveI : Group.IsPerfect X := ⟨hQX.1⟩
  have hne : d.Lf i ≠ ⊤ := by
    intro htop
    exact c.M_ne_top (hdM ▸ top_le_iff.mp (htop ▸ d.hLM i))
  have hKLi : CFSG.Open.IsKGroup ↥(d.Lf i) := c.standing.kProper.isKGroup (d.Lf i) hne
  have hKX : CFSG.Open.IsKGroup X := CFSG.Open.IsKGroup.quotient hKLi _
  have hrankX : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    have h1 : CFSG.pRank 3 X = CFSG.pRank 3 ↥(d.Lf i) :=
      CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three _
        (CFSG.GroupTheory.not_dvd_card_of_isPGroup
          (CFSG.pCore_isPGroup (p := 2) (G := ↥(d.Lf i))) Nat.prime_three
          (by norm_num : (3 : ℕ) ≠ 2))
    rw [h1, CFSG.SectionRank.pRank_coe_eq_openPRank, d.hrank i]
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center X) :=
    not_dvd_card_center_of_pRank_eq_one (q := 3) (by norm_num) hrankX
  let φ : ↥P₀ →* MulAut X := CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hPn i)
  let R : Subgroup (MulAut X) := φ.range
  have hR3 : IsPGroup 3 R :=
    IsPGroup.of_surjective hP03 φ.rangeRestrict φ.rangeRestrict_surjective
  let ψ : ↥(d.Lf i) →* MulAut X :=
    (MulAut.conj : X →* MulAut X).comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(d.Lf i)))
  let Inn : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range
  have hψmem : ∀ x : ↥(d.Lf i), ψ x ∈ Inn := fun x => ⟨QuotientGroup.mk' _ x, rfl⟩
  let ψInn : ↥(d.Lf i) →* Inn := ψ.codRestrict Inn hψmem
  have hψInn_surj : Function.Surjective ψInn := by
    rintro ⟨z, hz⟩
    obtain ⟨q, rfl⟩ := MonoidHom.mem_range.mp hz
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥(d.Lf i)) q
    exact ⟨y, Subtype.ext rfl⟩
  obtain ⟨Q, hQ⟩ := (d.isSylowOf_H i).exists_sylow_eq_subgroupOf
  let T : Sylow 3 Inn := Sylow.mapSurjective hψInn_surj Q
  let Sbar : Subgroup (MulAut X) := (T : Subgroup Inn).map Inn.subtype
  have hSbar_sylow : CFSG.ABGLocalTools.IsSylowOf 3 Sbar Inn := ⟨T, rfl⟩
  have hSbar_eq : Sbar = (Q : Subgroup ↥(d.Lf i)).map ψ := by
    change (T : Subgroup Inn).map Inn.subtype = (Q : Subgroup ↥(d.Lf i)).map ψ
    rw [Sylow.coe_mapSurjective, Subgroup.map_map]
    congr 1
  have hmapH_le (j : Fin 3) :
      Subgroup.map φ ((d.H j).subgroupOf P₀) ≤ (Q : Subgroup ↥(d.Lf i)).map ψ := by
    by_cases hji : j = i
    · subst j
      rintro s ⟨p, hp, rfl⟩
      have hpP0 : (p : G) ∈ d.H i := Subgroup.mem_subgroupOf.mp hp
      refine Subgroup.mem_map.mpr ⟨⟨(p : G), d.H_le_Lf i hpP0⟩, ?_, ?_⟩
      · show (⟨(p : G), d.H_le_Lf i hpP0⟩ : ↥(d.Lf i)) ∈ (Q : Subgroup ↥(d.Lf i))
        rw [hQ]
        exact Subgroup.mem_subgroupOf.mpr hpP0
      · show ψ ⟨(p : G), d.H_le_Lf i hpP0⟩ = φ p
        rw [CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk (hmM := hHP i hpP0)
          (hmL := d.H_le_Lf i hpP0)]
        rfl
    · have hbot : Subgroup.map φ ((d.H j).subgroupOf P₀) = ⊥ := by
        rw [Subgroup.map_eq_bot_iff]
        intro p hp
        exact MonoidHom.mem_ker.mpr
          (SylowThreeData.conjModPCore_H_eq_one d hPn hHP (i := i) (j := j) (fun h => hji h.symm)
            (Subgroup.mem_subgroupOf.mp hp))
      rw [hbot]
      exact bot_le
  have hmapS_le : Subgroup.map φ (d.S.subgroupOf P₀) ≤ (Q : Subgroup ↥(d.Lf i)).map ψ := by
    have hSsub : d.S.subgroupOf P₀ =
        ((d.H 0).subgroupOf P₀ ⊔ (d.H 1).subgroupOf P₀) ⊔ (d.H 2).subgroupOf P₀ := by
      rw [d.S_eq_sup, Subgroup.subgroupOf_sup (sup_le (hHP 0) (hHP 1)) (hHP 2),
        Subgroup.subgroupOf_sup (hHP 0) (hHP 1)]
    rw [hSsub, Subgroup.map_sup, Subgroup.map_sup]
    exact sup_le (sup_le (hmapH_le 0) (hmapH_le 1)) (hmapH_le 2)
  have hSbar_le_R : Sbar ≤ R := by
    rw [hSbar_eq]
    rintro s ⟨q, hqQ, rfl⟩
    have hqH : (q : G) ∈ d.H i := by
      have hq' : q ∈ (d.H i).subgroupOf (d.Lf i) := by
        rw [← hQ]
        exact hqQ
      exact Subgroup.mem_subgroupOf.mp hq'
    refine MonoidHom.mem_range.mpr ⟨⟨(q : G), hHP i hqH⟩, ?_⟩
    rw [CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk (hmM := hHP i hqH) (hmL := q.2)]
    rfl
  have hα3 : φ ⟨x, hxP0⟩ ^ 3 ∈ Sbar := by
    have hcube : φ ⟨x, hxP0⟩ ^ 3 = φ ⟨x ^ 3, P₀.pow_mem hxP0 3⟩ := by
      rw [← map_pow]
      congr 1
    rw [hcube, hSbar_eq]
    exact hmapS_le (Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hx3S))
  obtain ⟨s, hsSbar, hs3⟩ :=
    hK8 X hKX hQX hZ hrankX R Sbar hR3 hSbar_sylow hSbar_le_R (φ ⟨x, hxP0⟩)
      (MonoidHom.mem_range.mpr ⟨_, rfl⟩) hα3
  rw [hSbar_eq] at hsSbar
  obtain ⟨q, hqQ, hqs⟩ := Subgroup.mem_map.mp hsSbar
  have hqH : (q : G) ∈ d.H i := by
    have hq' : q ∈ (d.H i).subgroupOf (d.Lf i) := by
      rw [← hQ]
      exact hqQ
    exact Subgroup.mem_subgroupOf.mp hq'
  refine ⟨⟨(q : G), hqH⟩, ?_⟩
  have hφq : φ ⟨(q : G), hHP i hqH⟩ = s := by
    rw [CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk (hmM := hHP i hqH) (hmL := q.2)]
    rw [← hqs]
    rfl
  rw [hφq]
  exact hs3

theorem inf_iInf_normalizer_Lf_eq (c : Ctx812E G) (hK8 : OuterThreeSplit)
    (d : SylowThreeData G) (hdM : d.M = c.S.M) (hdL : d.L = c.L)
    (hcomp : ∀ i, CFSG.Yardstones.Mf4cdcdf2e013.Asc83CComponent c.S.M (d.Lf i))
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M) (hdS : d.S = P ⊓ c.L) :
    P ⊓ ⨅ i, Subgroup.normalizer (d.Lf i : Set G) = P ⊓ c.L := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := ⨅ i, Subgroup.normalizer (d.Lf i : Set G) with hN
  set P₀ : Subgroup G := P ⊓ N with hP₀
  change P₀ = P ⊓ c.L
  have hP03 : IsPGroup 3 P₀ := hP.isPGroup.to_le (by rw [hP₀]; exact inf_le_left)
  have hP0P : P₀ ≤ P := by rw [hP₀]; exact inf_le_left
  have hP0M : P₀ ≤ d.M := by rw [hdM]; exact hP0P.trans hP.le
  have hP0N (i : Fin 3) : P₀ ≤ Subgroup.normalizer (d.Lf i : Set G) := by
    rw [hP₀]
    exact inf_le_right.trans (hN.le.trans (iInf_le _ i))
  have hLnorm (i : Fin 3) : d.L ≤ Subgroup.normalizer (d.Lf i : Set G) := by
    rw [d.hL]
    exact sup_le (sup_le (d.hLnorm i 0) (d.hLnorm i 1)) (d.hLnorm i 2)
  have hP0NL : P₀ ≤ Subgroup.normalizer (d.L : Set G) := by
    have h1 : P₀ ≤ Subgroup.normalizer ((d.Lf 0 ⊔ d.Lf 1 : Subgroup G) : Set G) :=
      (le_inf (hP0N 0) (hP0N 1)).trans (Subgroup.inf_normalizer_le_normalizer_sup (d.Lf 0) (d.Lf 1))
    have h2 : P₀ ≤ Subgroup.normalizer (((d.Lf 0 ⊔ d.Lf 1) ⊔ d.Lf 2 : Subgroup G) : Set G) :=
      (le_inf h1 (hP0N 2)).trans
        (Subgroup.inf_normalizer_le_normalizer_sup (d.Lf 0 ⊔ d.Lf 1) (d.Lf 2))
    rw [d.hL]
    exact h2
  have hHP (i : Fin 3) : d.H i ≤ P₀ := by
    rw [hP₀]
    refine le_inf ?_ ?_
    · have h1 : d.H i ≤ d.S := d.H_le_S i
      rw [hdS] at h1
      exact h1.trans inf_le_left
    · rw [hN]
      exact le_iInf fun j => (d.H_le_Lf i).trans ((d.Lf_le_L i).trans (hLnorm j))
  have hge : P ⊓ c.L ≤ P₀ := by
    rw [hP₀]
    refine le_inf inf_le_left ?_
    rw [hN]
    refine le_iInf fun i => ?_
    rw [← hdL]
    exact inf_le_right.trans (hLnorm i)
  refine le_antisymm ?_ hge
  rw [hP₀]
  intro x hx
  have hxP : x ∈ P := hx.1
  have hxP0 : x ∈ P₀ := by rw [hP₀]; exact hx
  by_contra hxnot
  have hxLnot : x ∉ d.L := by
    intro hxL
    exact hxnot ⟨hxP, by rw [← hdL]; exact hxL⟩
  have hxM : x ∈ c.S.M := hdM ▸ hP0M hxP0
  obtain ⟨n, hn⟩ := hP03.exists_card_eq
  have hxn : x ^ (3 ^ n) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ← hn]
    exact Subgroup.orderOf_dvd_natCard P₀ hxP0
  have hex : ∃ j, x ^ (3 ^ j) ∈ d.L := ⟨n, by rw [hxn]; exact d.L.one_mem⟩
  let j := Nat.find hex
  have hj_spec : x ^ (3 ^ j) ∈ d.L := Nat.find_spec hex
  have hj_pos : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · exfalso
      rw [h0] at hj_spec
      exact hxLnot (by simpa using hj_spec)
    · exact hpos
  let y : G := x ^ (3 ^ (j - 1))
  have hyP0 : y ∈ P₀ := P₀.pow_mem hxP0 _
  have hyL : y ∉ d.L := by
    intro hmem
    exact Nat.find_min hex (Nat.sub_one_lt (Nat.ne_of_gt hj_pos)) hmem
  have hy3 : y ^ 3 = x ^ (3 ^ j) := by
    have h1 : 3 ^ (j - 1) * 3 = 3 ^ j := by
      rw [← pow_succ, Nat.sub_add_cancel hj_pos]
    show (x ^ (3 ^ (j - 1))) ^ 3 = x ^ (3 ^ j)
    rw [← pow_mul, h1]
  have hy3S : y ^ 3 ∈ d.S := by
    rw [hdS]
    refine ⟨hP0P (P₀.pow_mem hyP0 3), ?_⟩
    rw [← hdL, hy3]
    exact hj_spec
  choose k hk3 using fun i =>
    exists_mem_H_mul_pow_three_eq_one c hK8 d hdM hcomp hP03 hP0M hP0N hHP i hyP0 hy3S
  let y' : G := (k 0 : G) * (k 1 : G) * (k 2 : G) * y
  have hy'P0 : y' ∈ P₀ :=
    P₀.mul_mem (P₀.mul_mem (P₀.mul_mem (hHP 0 (k 0).2) (hHP 1 (k 1).2))
      (hHP 2 (k 2).2)) hyP0
  have hy'L : y' ∉ d.L := by
    intro hmem
    have h0L : (k 0 : G) ∈ d.L := (d.H_le_Lf 0).trans (d.Lf_le_L 0) (k 0).2
    have h1L : (k 1 : G) ∈ d.L := (d.H_le_Lf 1).trans (d.Lf_le_L 1) (k 1).2
    have h2L : (k 2 : G) ∈ d.L := (d.H_le_Lf 2).trans (d.Lf_le_L 2) (k 2).2
    have hprod : (k 0 : G) * (k 1 : G) * (k 2 : G) ∈ d.L :=
      d.L.mul_mem (d.L.mul_mem h0L h1L) h2L
    have hyeq : ((k 0 : G) * (k 1 : G) * (k 2 : G))⁻¹ * y' = y := by
      show ((k 0 : G) * (k 1 : G) * (k 2 : G))⁻¹ *
        ((k 0 : G) * (k 1 : G) * (k 2 : G) * y) = y
      group
    exact hyL (hyeq ▸ d.L.mul_mem (d.L.inv_mem hprod) hmem)
  have hfac (i : Fin 3) :
      (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i)) ⟨y', hy'P0⟩ =
        (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i)) ⟨(k i : G), hHP i (k i).2⟩ *
        (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i)) ⟨y, hyP0⟩ := by
    have hy'_eq : (⟨y', hy'P0⟩ : ↥P₀) =
        ⟨(k 0 : G), hHP 0 (k 0).2⟩ * ⟨(k 1 : G), hHP 1 (k 1).2⟩ *
          ⟨(k 2 : G), hHP 2 (k 2).2⟩ * ⟨y, hyP0⟩ := Subtype.ext rfl
    rw [hy'_eq, map_mul, map_mul, map_mul]
    have hkill : (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i))
          ⟨(k 0 : G), hHP 0 (k 0).2⟩ *
        (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i)) ⟨(k 1 : G), hHP 1 (k 1).2⟩ *
        (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i)) ⟨(k 2 : G), hHP 2 (k 2).2⟩ =
        (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i)) ⟨(k i : G), hHP i (k i).2⟩ := by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 from by fin_cases i <;> simp) with rfl | rfl | rfl
      · rw [SylowThreeData.conjModPCore_H_eq_one d hP0N hHP (i := 0) (j := 1) (by decide) (k 1).2,
          SylowThreeData.conjModPCore_H_eq_one d hP0N hHP (i := 0) (j := 2) (by decide) (k 2).2,
          mul_one, mul_one]
      · rw [SylowThreeData.conjModPCore_H_eq_one d hP0N hHP (i := 1) (j := 0) (by decide) (k 0).2,
          SylowThreeData.conjModPCore_H_eq_one d hP0N hHP (i := 1) (j := 2) (by decide) (k 2).2,
          one_mul, mul_one]
      · rw [SylowThreeData.conjModPCore_H_eq_one d hP0N hHP (i := 2) (j := 0) (by decide) (k 0).2,
          SylowThreeData.conjModPCore_H_eq_one d hP0N hHP (i := 2) (j := 1) (by decide) (k 1).2,
          one_mul, one_mul]
    rw [hkill]
  have hfixcube (i : Fin 3) :
      (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i)) ⟨y' ^ 3, P₀.pow_mem hy'P0 3⟩ = 1 := by
    rw [show (⟨y' ^ 3, P₀.pow_mem hy'P0 3⟩ : ↥P₀) = ⟨y', hy'P0⟩ ^ 3 from Subtype.ext rfl, map_pow,
      hfac i, hk3 i]
  by_cases hy'3 : y' ^ 3 = 1
  ·
    have hy'AA : y' ∈ d.AA :=
      mem_AA_of_pow_three_eq_one c d hdM hdL (hdM ▸ hP0M hy'P0)
        (by
          rw [hdS]
          refine Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hP0P hy'P0), ?_⟩
          rw [← hdL]
          exact hP0NL hy'P0)
        (fun i => hP0N i hy'P0) hy'3
    exact hy'L (d.AA_le_L hy'AA)
  ·
    have hcP0 : y' ^ 3 ∈ P₀ := P₀.pow_mem hy'P0 3
    obtain ⟨n₀, hn₀⟩ := hP03.exists_card_eq
    have hdvd0 : orderOf (y' ^ 3) ∣ 3 ^ n₀ := by
      rw [← hn₀]
      exact Subgroup.orderOf_dvd_natCard P₀ hcP0
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd0
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · exfalso
        exact hy'3 (by rw [h0] at hm; simpa using hm)
      · exact hpos
    let c₀ : G := (y' ^ 3) ^ (3 ^ (m - 1))
    have hc0P0 : c₀ ∈ P₀ := P₀.pow_mem hcP0 _
    have hc03 : c₀ ^ 3 = 1 := by
      have h1 : 3 ^ (m - 1) * 3 = 3 ^ m := by
        rw [← pow_succ, Nat.sub_add_cancel hmpos]
      show ((y' ^ 3) ^ (3 ^ (m - 1))) ^ 3 = 1
      rw [← pow_mul, h1, ← hm, pow_orderOf_eq_one]
    have hc0ne : c₀ ≠ 1 := by
      intro h1
      have hdvd : 3 ^ m ∣ 3 ^ (m - 1) := by
        rw [← hm, orderOf_dvd_iff_pow_eq_one]
        exact h1
      have hle : 3 ^ m ≤ 3 ^ (m - 1) :=
        Nat.le_of_dvd (pow_pos (by norm_num : (0:ℕ) < 3) _) hdvd
      have hlt : 3 ^ (m - 1) < 3 ^ m :=
        Nat.pow_lt_pow_right (by norm_num) (Nat.sub_one_lt (Nat.ne_of_gt hmpos))
      omega
    have hc0fix (i : Fin 3) :
        (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i)) ⟨c₀, hc0P0⟩ = 1 := by
      show (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i))
        ⟨(y' ^ 3) ^ (3 ^ (m - 1)), hc0P0⟩ = 1
      rw [show (⟨(y' ^ 3) ^ (3 ^ (m - 1)), hc0P0⟩ : ↥P₀) =
          ⟨y' ^ 3, hcP0⟩ ^ (3 ^ (m - 1)) from Subtype.ext rfl, map_pow, hfixcube i, one_pow]
    have hc0AA : c₀ ∈ d.AA :=
      mem_AA_of_pow_three_eq_one c d hdM hdL (hdM ▸ hP0M hc0P0)
        (by
          rw [hdS]
          refine Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hP0P hc0P0), ?_⟩
          rw [← hdL]
          exact hP0NL hc0P0)
        (fun i => hP0N i hc0P0) hc03
    have hc0S : c₀ ∈ d.S := d.AA_le_S hc0AA
    have hcen (i j : Fin 3) (hij : i ≠ j) : d.H j ≤ Subgroup.centralizer (d.H i : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h := (d.H_commute_incl i j hij ⟨a, ha⟩ ⟨b, hb⟩).eq
      simpa using congrArg Subtype.val h
    have hNH0 : d.H 2 ≤ Subgroup.normalizer (d.H 0 : Set G) :=
      (hcen 0 2 (by decide)).trans (Subgroup.centralizer_le_normalizer _)
    have hNH1 : d.H 2 ≤ Subgroup.normalizer (d.H 1 : Set G) :=
      (hcen 1 2 (by decide)).trans (Subgroup.centralizer_le_normalizer _)
    have hnorm2 : d.H 2 ≤ Subgroup.normalizer (((d.H 0 ⊔ d.H 1) : Subgroup G) : Set G) :=
      (le_inf hNH0 hNH1).trans
        (Subgroup.inf_normalizer_le_normalizer_sup (d.H 0) (d.H 1))
    have hnorm1 : d.H 1 ≤ Subgroup.normalizer (d.H 0 : Set G) :=
      (hcen 0 1 (by decide)).trans (Subgroup.centralizer_le_normalizer _)
    have hc0mul : c₀ ∈ (((d.H 0 ⊔ d.H 1) : Subgroup G) : Set G) * (d.H 2 : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm2, ← d.S_eq_sup]
      exact hc0S
    obtain ⟨u, hu, w2, hw2, hu2⟩ := hc0mul
    have humul : u ∈ (d.H 0 : Set G) * (d.H 1 : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm1]
      exact hu
    obtain ⟨w0, hw0, w1, hw1, hw01⟩ := humul
    let w : Fin 3 → G := ![w0, w1, w2]
    have hwH : ∀ i, w i ∈ d.H i := by
      intro i
      fin_cases i <;> first
        | simpa [w] using hw0
        | simpa [w] using hw1
        | simpa [w] using hw2
    have hc0eq : c₀ = w 0 * w 1 * w 2 := by
      rw [show w 0 = w0 from rfl, show w 1 = w1 from rfl, show w 2 = w2 from rfl]
      rw [← hu2, ← hw01]
    have hwi1 : ∀ i : Fin 3,
        (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i))
          ⟨w i, hHP i (hwH i)⟩ = 1 := by
      intro i
      have hprod : (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i))
            ⟨w 0, hHP 0 (hwH 0)⟩ *
          (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i)) ⟨w 1, hHP 1 (hwH 1)⟩ *
          (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i)) ⟨w 2, hHP 2 (hwH 2)⟩ = 1 := by
        have h1 : (⟨c₀, hc0P0⟩ : ↥P₀) =
            ⟨w 0, hHP 0 (hwH 0)⟩ * ⟨w 1, hHP 1 (hwH 1)⟩ * ⟨w 2, hHP 2 (hwH 2)⟩ := by
          apply Subtype.ext
          exact hc0eq
        have h2 : (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i)) ⟨c₀, hc0P0⟩ =
            (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i)) ⟨w 0, hHP 0 (hwH 0)⟩ *
              (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i)) ⟨w 1, hHP 1 (hwH 1)⟩ *
              (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i)) ⟨w 2, hHP 2 (hwH 2)⟩ := by
          rw [h1, map_mul, map_mul]
        rw [← h2, hc0fix i]
      have hkill : (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i))
            ⟨w 0, hHP 0 (hwH 0)⟩ *
          (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i)) ⟨w 1, hHP 1 (hwH 1)⟩ *
          (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i)) ⟨w 2, hHP 2 (hwH 2)⟩ =
          (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i)) ⟨w i, hHP i (hwH i)⟩ := by
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 from by fin_cases i <;> simp) with rfl | rfl | rfl
        · rw [SylowThreeData.conjModPCore_H_eq_one d hP0N hHP (i := 0) (j := 1) (by decide)
              (hwH 1),
            SylowThreeData.conjModPCore_H_eq_one d hP0N hHP (i := 0) (j := 2) (by decide)
              (hwH 2),
            mul_one, mul_one]
        · rw [SylowThreeData.conjModPCore_H_eq_one d hP0N hHP (i := 1) (j := 0) (by decide)
              (hwH 0),
            SylowThreeData.conjModPCore_H_eq_one d hP0N hHP (i := 1) (j := 2) (by decide)
              (hwH 2),
            one_mul, mul_one]
        · rw [SylowThreeData.conjModPCore_H_eq_one d hP0N hHP (i := 2) (j := 0) (by decide)
              (hwH 0),
            SylowThreeData.conjModPCore_H_eq_one d hP0N hHP (i := 2) (j := 1) (by decide)
              (hwH 1),
            one_mul, one_mul]
      rw [← hkill]
      exact hprod
    have hfall : ∀ i : Fin 3, w i = 1 := by
      intro i
      refine SylowThreeData.eq_one_of_mem_H_of_forall_commutator_mem d i (hwH i) ?_ ?_
      · obtain ⟨hNi, hQi⟩ := (hcomp i).2.2.2
        let Xi : Type := ↥(d.Lf i) ⧸ CFSG.Open.pCore 2 ↥(d.Lf i)
        have hQi' : CFSG.Open.IsQuasisimple Xi := hQi
        haveI : Group.IsPerfect Xi := ⟨hQi'.1⟩
        have hrankXi : CFSG.Open.pRank 3 (⊤ : Subgroup Xi) = 1 := by
          rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
          have h1 : CFSG.pRank 3 Xi = CFSG.pRank 3 ↥(d.Lf i) :=
            CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three _
              (CFSG.GroupTheory.not_dvd_card_of_isPGroup
                (CFSG.pCore_isPGroup (p := 2) (G := ↥(d.Lf i))) Nat.prime_three
                (by norm_num : (3 : ℕ) ≠ 2))
          rw [h1, CFSG.SectionRank.pRank_coe_eq_openPRank, d.hrank i]
        exact not_dvd_card_center_of_pRank_eq_one (q := 3) (by norm_num) hrankXi
      · have hmem : w i ∈ ((CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0N i)).ker.map
            P₀.subtype) :=
          ⟨⟨w i, hHP i (hwH i)⟩, MonoidHom.mem_ker.mpr (hwi1 i), rfl⟩
        exact ((CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 (d.Lf i) P₀ (hP0N i)).mp hmem).2
    have hc01 : c₀ = 1 := by
      rw [hc0eq, hfall 0, hfall 1, hfall 2, mul_one, mul_one]
    exact hc0ne hc01

end Ctx812E

namespace Ctx812

theorem inf_iInf_normalizer_Lf_eq (c : Ctx812 G) (hK8 : OuterThreeSplit)
    (d : SylowThreeData G) (hdM : d.M = c.S.M) (hdL : d.L = c.L)
    (hcomp : ∀ i, CFSG.Yardstones.Mf4cdcdf2e013.Asc83CComponent c.S.M (d.Lf i))
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M) (hdS : d.S = P ⊓ c.L) :
    P ⊓ ⨅ i, Subgroup.normalizer (d.Lf i : Set G) = P ⊓ c.L :=
  Ctx812E.inf_iInf_normalizer_Lf_eq c.toCtx812E hK8 d hdM hdL hcomp hP hdS

end Ctx812

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
