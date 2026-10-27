module

import CFSG.RankThree.PartTwo.Sec16.Item166CtrLB
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
public import CFSG.RankThree.PartTwo.Sec17.Item17Setup
import CFSG.RankThree.PartTwo.Sec17.Item17Res8ProofKMd
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofDelta
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.GroupTheory.SteinbergCEThetaSubnormalDichotomy
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kd166

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec11
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem inf_le_theta_of_types {X N : Subgroup G}
    (htypes : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
        CFSG.Blueprint.NativeSporadic.ON ∨
      Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) ∨
      IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hN : Nat.Coprime 3 (Nat.card N)) :
    X ⊓ N ≤ inSubgroup (aschbacherSolvableCore 3) X := by
  have hnormal : ((X ⊓ N).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      ((le_inf Subgroup.le_normalizer hXN).trans Subgroup.inf_normalizer_le_normalizer_inf)
  haveI := hnormal
  have hcard : Nat.card ((X ⊓ N).subgroupOf X) ∣ Nat.card N :=
    (Proof17Res8.card_subgroupOf_dvd (X ⊓ N) X).trans (Subgroup.card_dvd_of_le inf_le_right)
  have h3 : ¬ 3 ∣ Nat.card ((X ⊓ N).subgroupOf X) := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN (h.trans hcard)
  have hle : (X ⊓ N).subgroupOf X ≤ aschbacherSolvableCore 3 ↥X :=
    Proof17Res8.le_theta_of_normal_of_types htypes ((X ⊓ N).subgroupOf X) h3
  intro y hy
  exact Subgroup.mem_map.mpr ⟨⟨y, hy.1⟩, hle (Subgroup.mem_subgroupOf.mpr hy), rfl⟩

theorem sSup_le_centralizer_of_subset {d : G} {𝒳 : Set (Subgroup G)}
    (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d) : sSup 𝒳 ≤ Subgroup.centralizer ({d} : Set G) :=
  sSup_le fun Y hY => le_centralizer_of_mem_thetaComponentsAt (h𝒳 hY)

theorem pPrimeCoreOf_le_normalizer_sSup_of_types {d : G}
    {𝒳 : Set (Subgroup G)} (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d)
    (htypes : Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
        CFSG.Blueprint.NativeSporadic.ON ∨
      Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
        (alternatingGroup (Fin 6)) ∨
      IsCentralProductA6Covers (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))) :
    pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ≤
      Subgroup.normalizer ((sSup 𝒳 : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({d} : Set G) with hC
  set X := sSup 𝒳 with hX
  have hXC : X ≤ C := by
    rw [hX, hC]
    exact sSup_le fun Y hY => le_centralizer_of_mem_thetaComponentsAt (h𝒳 hY)
  refine Sec14.le_normalizer_sSup ?_
  intro Y hY
  have hYin : Y ∈ thetaComponentsIn C := h𝒳 hY
  obtain ⟨hYC, hY'⟩ := mem_thetaComponentsIn_iff.mp hYin
  have hUs : (CFSG.pPrimeCore 3 ↥C).IsSubnormal :=
    (CFSG.pPrimeCore_normal (p := 3) (G := ↥C)).isSubnormal
  rcases GroupTheory.theta_component_subnormal_subgroup_dichotomy Nat.prime_three hY' hUs with
    hYU | ⟨hUN, -⟩
  · exfalso
    have hYX : Y ≤ X := by
      rw [hX]
      exact le_sSup hY
    have hYO : Y ≤ pPrimeCoreOf 3 C := by
      rw [pPrimeCoreOf]
      have h := Subgroup.map_mono (f := C.subtype) hYU
      rwa [Subgroup.map_subgroupOf_eq_of_le hYC] at h
    have hXN : X ≤ Subgroup.normalizer (pPrimeCoreOf 3 C : Set G) :=
      hXC.trans (le_normalizer_pPrimeCoreOf 3 C)
    have hYθ : Y ≤ inSubgroup (aschbacherSolvableCore 3) X :=
      (le_inf hYX hYO).trans
        (inf_le_theta_of_types (X := X) (N := pPrimeCoreOf 3 C) htypes hXN
          (coprime_card_pPrimeCoreOf 3 C))
    have hYsolv : Group.IsSolvable Y := by
      haveI : Group.IsSolvable ↥(inSubgroup (aschbacherSolvableCore 3) X) :=
        Proof171Steps.isSolvable_theta X
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hYθ)
    have hYbot : Y = ⊥ :=
      CFSG.RankThree.GroupTheory.eq_bot_of_isPerfect_of_isSolvable
        (Sec6.isPerfect_of_mem_thetaComponentsAt (h𝒳 hY)) hYsolv
    apply Sec6.theta_ne_of_mem_thetaComponentsAt (h𝒳 hY)
    rw [hYbot]
    exact le_bot_iff.mp (Subgroup.map_subtype_le _)
  · have hmap : pPrimeCoreOf 3 C ≤ Subgroup.normalizer (Y : Set G) := by
      calc pPrimeCoreOf 3 C = (CFSG.pPrimeCore 3 ↥C).map C.subtype := rfl
        _ ≤ (Subgroup.normalizer (Y.subgroupOf C : Set ↥C)).map C.subtype :=
          Subgroup.map_mono hUN
        _ ≤ Subgroup.normalizer ((Y.subgroupOf C).map C.subtype : Set G) :=
          Subgroup.le_normalizer_map C.subtype
        _ = Subgroup.normalizer (Y : Set G) := by
          rw [Subgroup.map_subgroupOf_eq_of_le hYC]
    simpa [hC] using hmap

private lemma false_of_delta_eq_pPrimeCoreOf_sup
    {d : G} (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d)
    (hΔ1 : delta A (lB A) (Subgroup.centralizer ({d} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := h.toSec14Std.isE27
  have hdD : d ∈ Subgroup.closure ({c, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem c (Set.mem_singleton d))
  have hB : IsHyperplane A (Subgroup.closure {c, d}) :=
    Ctr166.isHyperplane_closure_cd h hJ hdA hd1 hdc
  have hcfg : IsLBConfig A (Subgroup.closure {c, d}) c d L :=
    Ctr166.isLBConfig_closure_cd_of_threeCentral h hJ hdc
  have hLBΔ : lB A (Subgroup.closure {c, d}) ≤
      delta A (lB A) (Subgroup.centralizer ({d} : Set G)) :=
    Desc143X.lB_le_delta h.toSec14Std hB hcfg hdD
  have hdLB : d ∈ lB A (Subgroup.closure {c, d}) :=
    Ctr166.mem_lB_closure h hJ hdA hd1 hdc
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hA.1.2 d hdA) hd1
  have h3LB : 3 ∣ Nat.card (lB A (Subgroup.closure {c, d})) := by
    have h := Subgroup.orderOf_dvd_natCard (lB A (Subgroup.closure {c, d})) hdLB
    rwa [hd3] at h
  have h3Δ : 3 ∣ Nat.card
      (delta A (lB A) (Subgroup.centralizer ({d} : Set G))) :=
    h3LB.trans (Subgroup.card_dvd_of_le hLBΔ)
  rw [hΔ1] at h3Δ
  have hO3 : IsPiSubgroup (piCompl 3)
      (pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))) :=
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_card_pPrimeCoreOf 3 _))
  have hW3 : IsPiSubgroup (piCompl 3)
      (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :=
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_card_pPrimeCoreOf 3 _))
  have hWN : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
      Subgroup.normalizer
        (pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) : Set G) :=
    ((pPrimeCoreOf_le 3 _).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdA))).trans
        (le_normalizer_pPrimeCoreOf 3 _)
  have hOW3 : IsPiSubgroup (piCompl 3)
      (pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :=
    (by rw [sup_comm]; exact isPiSubgroup_piCompl_sup hW3 hO3 hWN)
  exact absurd h3Δ ((isPiSubgroup_piCompl_iff Nat.prime_three _).mp hOW3)

private lemma false_of_zpowers_eq_at_d {b' d d' : G}
    (hb'c : Subgroup.zpowers b' = Subgroup.zpowers c) (hc3 : orderOf c = 3)
    (hcL : c ∉ L) (hdL : d ∈ L) (hd1 : d ≠ 1) (hd'L : d' ∈ L)
    (hd'3 : orderOf d' = 3) (hcd : Commute c d')
    (hclos : d ∈ Subgroup.closure {b', d'})
    (hne : Subgroup.zpowers d ≠ Subgroup.zpowers d') :
    False := by
  have hpair : Subgroup.closure ({b', d'} : Set G) =
      Subgroup.closure ({c, d'} : Set G) := by
    rw [Set.pair_comm b' d', Item1119Sym.closure_pair_eq_of_zpowers_eq d' b' c hb'c,
      Set.pair_comm d' c]
  have hclos' : d ∈ Subgroup.closure ({c, d'} : Set G) := by
    rw [← hpair]
    exact hclos
  have hdm : d ∈ Subgroup.zpowers d' :=
    Sec17.mem_zpowers_of_mem_closure_pair (L := L) (c := c) (d := d') (b := d)
      hc3 hcL hd'L hcd hclos' hdL
  exact hne (Sec17.zpowers_eq_of_mem_zpowers hd'3 hdm hd1)

theorem exists_case2ii_at_d
    (h143 : Ronan148Q.Item143QS14) (h : Sec17Std G A c L Y₀)
    (hΩ : omegaA A = {Subgroup.zpowers c})
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    ∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 d ∧ 𝒳.Nonempty ∧
      delta A (lB A) (Subgroup.centralizer ({d} : Set G)) =
        pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ sSup 𝒳 ∧
      Ronan148Q.Inv143Q A d d (sSup 𝒳) ∧
      (Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
          CFSG.Blueprint.NativeSporadic.ON ∨
        Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
          (alternatingGroup (Fin 6)) ∨
        IsCentralProductA6Covers (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := h.toSec14Std.isE27
  obtain ⟨hcL, h9, -⟩ := Sec14.j2_point_facts h.toSec13Data hJ
  obtain ⟨hdL, -⟩ := id hdc
  have hdΩ : Subgroup.zpowers d ∉ omegaA A := by
    rw [hΩ, Set.mem_singleton_iff]
    intro hzd
    exact hcL (Subgroup.zpowers_le.mpr hdL (hzd ▸ Subgroup.mem_zpowers c))
  obtain ⟨Q, hQ⟩ := maxInvariantPiSubgroups_nonempty
    (delta A (lB A) (Subgroup.centralizer ({d} : Set G))) A (piCompl 3)
  obtain ⟨-, hcase⟩ := h143 G A c L h.toSec14Std d hdA hd1 hdΩ Q hQ
  rcases hcase with
    hΔ1 | ⟨b', d', Lb', hb'Ω, hLb', -, hd'A, hd'1, hd'c, hclos, X, hΔX, hCN, hcase2⟩
  · exact (false_of_delta_eq_pPrimeCoreOf_sup h hJ hdA hd1 hdc hΔ1).elim
  · have hb'c : Subgroup.zpowers b' = Subgroup.zpowers c := by
      rw [hΩ] at hb'Ω
      exact hb'Ω
    have h3L : 3 ∣ Nat.card L := by
      have hdvd : Nat.card (A ⊓ L : Subgroup G) ∣ Nat.card L :=
        Subgroup.card_dvd_of_le inf_le_right
      rw [h9] at hdvd
      exact dvd_trans (by norm_num) hdvd
    have hLb'L : Lb' = L :=
      Proof1515.eq_of_mem_lA_of_zpowers_eq h.toSec14Std h3L hb'c hLb'
    rcases hcase2 with ⟨-, -, hne⟩ | ⟨-, ⟨𝒳, h𝒳, h𝒳ne, hXeq⟩, htypes⟩
    · have hd'L : d' ∈ L := by
        have h := hd'c.1
        rwa [hLb'L] at h
      have hd'3 : orderOf d' = 3 := orderOf_eq_prime (hA.1.2 d' hd'A) hd'1
      have hcd : Commute c d' :=
        congrArg Subtype.val
          (hA.1.1.is_comm.comm ⟨c, h.toSec13Data.mem_A⟩ ⟨d', hd'A⟩)
      exact (false_of_zpowers_eq_at_d hb'c h.toSec13Data.orderOf_eq hcL hdL hd1 hd'L
        hd'3 hcd hclos hne).elim
    · subst X
      have hinv : Ronan148Q.Inv143Q A d d (sSup 𝒳) := by
        rcases hCN with h | ⟨-, hXθ, hA6, hN⟩
        · exact Or.inl h
        · exact Or.inr ⟨rfl, hXθ, hA6, hN⟩
      exact ⟨𝒳, h𝒳, h𝒳ne, hΔX, hinv, htypes⟩

theorem lB_le_sSup_of_case2ii
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d)
    {𝒳 : Set (Subgroup G)} (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d)
    (hΔ : delta A (lB A) (Subgroup.centralizer ({d} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ sSup 𝒳)
    (hinv : Ronan148Q.Inv143Q A d d (sSup 𝒳))
    (htypes : Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
        CFSG.Blueprint.NativeSporadic.ON ∨
      Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
        (alternatingGroup (Fin 6)) ∨
      IsCentralProductA6Covers (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))) :
    lB A (Subgroup.closure {c, d}) ≤ sSup 𝒳 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) with hO
  set W := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hW
  set X := sSup 𝒳 with hX
  have hΔ' : delta A (lB A) (Subgroup.centralizer ({d} : Set G)) = O ⊔ W ⊔ X := hΔ
  have hdD : d ∈ Subgroup.closure ({c, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem c (Set.mem_singleton d))
  have hB : IsHyperplane A (Subgroup.closure {c, d}) :=
    Ctr166.isHyperplane_closure_cd h hJ hdA hd1 hdc
  have hcfg : IsLBConfig A (Subgroup.closure {c, d}) c d L :=
    Ctr166.isLBConfig_closure_cd_of_threeCentral h hJ hdc
  have hLBΔ : lB A (Subgroup.closure {c, d}) ≤
      delta A (lB A) (Subgroup.centralizer ({d} : Set G)) :=
    Desc143X.lB_le_delta h.toSec14Std hB hcfg hdD
  have hLBK : lB A (Subgroup.closure {c, d}) ≤
      oPrimeResidualOf 3 (delta A (lB A) (Subgroup.centralizer ({d} : Set G))) :=
    Proof171Steps.lB_le_oPrimeResidualOf h.toSec14Std hB hLBΔ
  rw [Sec14.oPrimeResidualOf_eq_closure] at hLBK
  refine hLBK.trans ((Subgroup.closure_le X).mpr ?_)
  rintro x ⟨hxD, k, hxk⟩
  have hOW : W ≤ Subgroup.normalizer ((O ⊔ X : Subgroup G) : Set G) := by
    have hWCA : W ≤ Subgroup.centralizer (A : Set G) := by
      rw [hW]
      exact pPrimeCoreOf_le 3 _
    exact hWCA.trans (by simpa only [hO, hX] using hinv.centralizer_le hdA)
  have hW3 : Nat.Coprime 3 (Nat.card W) := by
    rw [hW]
    exact coprime_card_pPrimeCoreOf 3 _
  have hx1 : x ∈ (O ⊔ X) ⊔ W := by
    rw [hΔ'] at hxD
    rwa [sup_right_comm] at hxD
  have hxOX : x ∈ O ⊔ X :=
    Sec14.mem_left_of_pow_prime_pow Nat.prime_three hOW hW3 hx1 hxk
  have hON : O ≤ Subgroup.normalizer (X : Set G) := by
    rw [hO, hX]
    exact pPrimeCoreOf_le_normalizer_sSup_of_types h𝒳 htypes
  have hO3 : Nat.Coprime 3 (Nat.card O) := by
    rw [hO]
    exact coprime_card_pPrimeCoreOf 3 _
  have hxXO : x ∈ X ⊔ O := by
    rwa [sup_comm] at hxOX
  exact Sec14.mem_left_of_pow_prime_pow Nat.prime_three hON hO3 hxXO hxk

end CFSG.RankThree.PartTwo.Sec16.Kd166
