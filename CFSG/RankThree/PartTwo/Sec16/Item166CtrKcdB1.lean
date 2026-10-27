module

public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.KFacts.KS166J2A5Three

import CFSG.RankThree.PartTwo.Sec16.Item166CtrStar
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofCover
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.GroupTheory.PCore.InfPCoreOf
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.GroupTheory.CoprimeCovering
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec16.Ctr166

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

private lemma mem_A_of_mem_pair {c d b : G} (hc : c ∈ A) (hd : d ∈ A)
    (hb : b ∈ ({c * d, c * d ^ 2} : Set G)) : b ∈ A := by
  rcases Set.mem_insert_iff.mp hb with h | h
  · rw [h]; exact A.mul_mem hc hd
  · rw [Set.mem_singleton_iff.mp h]; exact A.mul_mem hc (A.pow_mem hd 2)

theorem commutator_zpowers_c_le_pCoreOf (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    (h1523 : Item1523R) {J : Subgroup G} (hJY : J ≤ Y₀)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) :
    ⁅J, Subgroup.zpowers c⁆ ≤ CFSG.Open.pCoreOf 2 J := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := CFSG.Open.pCoreOf 2 J with hN
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hcN : c ∈ Subgroup.normalizer (N : Set G) :=
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J) (hAJ hcA)
  have hmemN : ∀ j ∈ J, ⁅j, c⁆ ∈ N := by
    intro j hj
    have hjY : j ∈ Y₀ := hJY hj
    have hconj : c * j * c⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hAJ hcA) j).mp hj
    have hjcJ : ⁅j, c⁆ ∈ J := by
      rw [commutatorElement_def]
      have : j * c * j⁻¹ * c⁻¹ = j * (c * j * c⁻¹)⁻¹ := by group
      rw [this]
      exact J.mul_mem hj (J.inv_mem hconj)
    have hjcP : ⁅j, c⁆ ∈ CFSG.Open.pCoreOf 2 Y₀ :=
      commutatorElement_mem_pCoreOf_y0 h hJ h1523 j hjY
    exact CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hJY ⟨hjcJ, hjcP⟩
  have hcC : c ∈ commutatorInSubgroup J N :=
    mem_commutatorInSubgroup.mpr ⟨hcN, hmemN⟩
  have hsub : Subgroup.zpowers c ≤ commutatorInSubgroup J N :=
    Subgroup.zpowers_le.mpr hcC
  exact Subgroup.commutator_le.mpr fun j hj k hk =>
    (mem_commutatorInSubgroup.mp (hsub hk)).2 j hj

theorem commutator_zpowers_d_le_pCoreOf
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    (h1523 : Item1523R) (hK3 : KFacts.KS166J2A5Three) {J : Subgroup G} (hJY : J ≤ Y₀)
    (hJperf : Group.IsPerfect ↥J)
    (hJA5 : Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)))
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) {d : G} (hdA : d ∈ A)
    (hdc : IsThreeCentralIn L d) :
    ⁅J, Subgroup.zpowers d⁆ ≤ CFSG.Open.pCoreOf 2 J := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q : Subgroup ↥Y₀ := CFSG.pCore 2 ↥Y₀ with hQ
  set JY : Subgroup ↥Y₀ := J.subgroupOf Y₀ with hJYdef
  set π : ↥Y₀ →* ↥Y₀ ⧸ Q := QuotientGroup.mk' Q with hπ
  set Jstar : Subgroup (↥Y₀ ⧸ Q) := JY.map π with hJstar
  set E : Subgroup (↥Y₀ ⧸ Q) := ((A ⊓ L).subgroupOf Y₀).map π with hE
  have hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
    have h1 := (h1523 G A c L h.toSec15R hJ Y₀ h.mem_y0Star).1
    rwa [inf_of_le_right h.le_y0] at h1
  have hYJ : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃*
      CFSG.Blueprint.NativeSporadic.J2) :=
    CFSG.RankThree.PartTwo.Sec17.PropU.nonempty_quotient_J2 h hJ hY
  have hEstar := card_map_inf_eq_nine h hJ
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    simpa only [E, π, Q] using hEstar.1
  have hEcard : Nat.card E = 9 := by
    simpa only [E, π, Q] using hEstar.2
  have hEnorm : E ≤ Subgroup.normalizer (Jstar : Set (↥Y₀ ⧸ Q)) := by
    simpa only [E, Jstar, π, JY] using map_inf_le_normalizer_star hJY hAJ
  have hKstar := hK3 (↥Y₀ ⧸ Q) hYJ Jstar (isPerfect_map_star hJY hJperf)
    (nonempty_map_star_quot_a5 hJY hJA5) E hEnorm hE3 hEcard
  obtain ⟨hdL, S, hdS, hSd⟩ := hdc
  have hdY : d ∈ Y₀ := h.le_y0 hdL
  have hdE : π ⟨d, hdY⟩ ∈ E :=
    Subgroup.mem_map.mpr
      ⟨⟨d, hdY⟩, Subgroup.mem_subgroupOf.mpr ⟨hdA, hdL⟩, rfl⟩
  let φ : ↥L →* ↥Y₀ ⧸ Q := π.comp (Subgroup.inclusion h.le_y0)
  have hLN : L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₀ : Set G) :=
    h.le_y0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀)
  have hset : (Y₀ : Set G) = (L : Set G) * (CFSG.Open.pCoreOf 2 Y₀ : Set G) := by
    conv_lhs => rw [hY]
    exact Subgroup.coe_mul_of_left_le_normalizer_right L _ hLN
  have hφsurj : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Q q
    have hy : (y : G) ∈ (L : Set G) * (CFSG.Open.pCoreOf 2 Y₀ : Set G) := by
      rw [← hset]; exact y.2
    obtain ⟨l, hlL, p, hpP, hlp⟩ := hy
    have hpY : p ∈ Y₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀ hpP
    have hpq : (⟨p, hpY⟩ : ↥Y₀) ∈ Q := by
      rw [hQ]
      exact (CFSG.mem_openPCoreOf_iff (⟨p, hpY⟩ : ↥Y₀)).mp hpP
    have hπp : π ⟨p, hpY⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hpq
    refine ⟨⟨l, hlL⟩, ?_⟩
    have hyl : (y : ↥Y₀) = (⟨l, h.le_y0 hlL⟩ : ↥Y₀) * ⟨p, hpY⟩ := Subtype.ext hlp.symm
    change φ ⟨l, hlL⟩ = π y
    rw [hyl, map_mul, hπp, mul_one]
    rfl
  have hφd : φ ⟨d, hdL⟩ = π ⟨d, hdY⟩ := rfl
  have hSmap : (S : Subgroup ↥L).map φ ≤
      Subgroup.centralizer ({π ⟨d, hdY⟩} : Set (↥Y₀ ⧸ Q)) := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := hx
    rw [Subgroup.mem_centralizer_singleton_iff, ← hφd]
    have hsd : s * (⟨d, hdL⟩ : ↥L) = (⟨d, hdL⟩ : ↥L) * s :=
      Subgroup.mem_centralizer_singleton_iff.mp (hSd hs)
    calc φ s * φ ⟨d, hdL⟩ = φ (s * ⟨d, hdL⟩) := by rw [map_mul]
      _ = φ ((⟨d, hdL⟩ : ↥L) * s) := by rw [hsd]
      _ = φ ⟨d, hdL⟩ * φ s := by rw [map_mul]
  let S' : Sylow 3 (↥Y₀ ⧸ Q) := S.mapSurjective (f := φ) hφsurj
  have hS'coe : (S' : Subgroup (↥Y₀ ⧸ Q)) = (S : Subgroup ↥L).map φ :=
    Sylow.coe_mapSurjective (f := φ) (P := S) hφsurj
  have hxS' : π ⟨d, hdY⟩ ∈ (S' : Subgroup (↥Y₀ ⧸ Q)) := by
    rw [hS'coe]
    exact Subgroup.mem_map.mpr ⟨⟨d, hdL⟩, hdS, rfl⟩
  have hS'le : (S' : Subgroup (↥Y₀ ⧸ Q)) ≤
      Subgroup.centralizer ({π ⟨d, hdY⟩} : Set (↥Y₀ ⧸ Q)) := by
    rw [hS'coe]
    exact hSmap
  have hxcent : π ⟨d, hdY⟩ ∈
      Subgroup.centralizer (Jstar : Set (↥Y₀ ⧸ Q)) :=
    hKstar (π ⟨d, hdY⟩) hdE ⟨S', hxS', hS'le⟩
  have hmemN : ∀ j ∈ J, ⁅j, d⁆ ∈ CFSG.Open.pCoreOf 2 J := by
    intro j hj
    have hjY : j ∈ Y₀ := hJY hj
    let u : ↥Y₀ := ⟨j, hjY⟩
    let v : ↥Y₀ := ⟨d, hdY⟩
    have hu : π u ∈ Jstar :=
      Subgroup.mem_map.mpr ⟨u, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
    have hcommu : ⁅π u, π v⁆ = 1 :=
      (Subgroup.mem_centralizer_iff_commutator_eq_one.mp hxcent) (π u) hu
    have hπcomm : π ⁅u, v⁆ = 1 := by
      rw [map_commutatorElement]
      simpa [v] using hcommu
    have hmemQ : ⁅u, v⁆ ∈ Q := (QuotientGroup.eq_one_iff _).mp hπcomm
    have hmemP : ((⁅u, v⁆ : ↥Y₀) : G) ∈ CFSG.Open.pCoreOf 2 Y₀ :=
      (CFSG.mem_openPCoreOf_iff (⁅u, v⁆)).mpr hmemQ
    have hcoe : ((⁅u, v⁆ : ↥Y₀) : G) = ⁅j, d⁆ := by
      simp [u, v, commutatorElement_def]
    have hmemPY : ⁅j, d⁆ ∈ CFSG.Open.pCoreOf 2 Y₀ := hcoe ▸ hmemP
    have hconj : d * j * d⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hAJ hdA) j).mp hj
    have hmemJ : ⁅j, d⁆ ∈ J := by
      rw [commutatorElement_def]
      have : j * d * j⁻¹ * d⁻¹ = j * (d * j * d⁻¹)⁻¹ := by group
      rw [this]
      exact J.mul_mem hj (J.inv_mem hconj)
    exact CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hJY ⟨hmemJ, hmemPY⟩
  have hdN : d ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 J : Set G) :=
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J) (hAJ hdA)
  have hdC : d ∈ commutatorInSubgroup J (CFSG.Open.pCoreOf 2 J) :=
    mem_commutatorInSubgroup.mpr ⟨hdN, hmemN⟩
  have hsub : Subgroup.zpowers d ≤ commutatorInSubgroup J (CFSG.Open.pCoreOf 2 J) :=
    Subgroup.zpowers_le.mpr hdC
  exact Subgroup.commutator_le.mpr fun j hj k hk =>
    (mem_commutatorInSubgroup.mp (hsub hk)).2 j hj

theorem commutator_zpowers_b_le_pCoreOf
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    (h1523 : Item1523R) (hK3 : KFacts.KS166J2A5Three) {J : Subgroup G} (hJY : J ≤ Y₀)
    (hJperf : Group.IsPerfect ↥J)
    (hJA5 : Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)))
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) {d : G} (hdA : d ∈ A)
    (hdc : IsThreeCentralIn L d) {b : G} (hb : b ∈ ({c * d, c * d ^ 2} : Set G)) :
    ⁅J, Subgroup.zpowers b⁆ ≤ CFSG.Open.pCoreOf 2 J := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := CFSG.Open.pCoreOf 2 J with hN
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hcN : c ∈ Subgroup.normalizer (N : Set G) :=
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J) (hAJ hcA)
  have hdN : d ∈ Subgroup.normalizer (N : Set G) :=
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J) (hAJ hdA)
  have hcc : ⁅J, Subgroup.zpowers c⁆ ≤ N :=
    commutator_zpowers_c_le_pCoreOf h hJ h1523 hJY hAJ
  have hdd : ⁅J, Subgroup.zpowers d⁆ ≤ N :=
    commutator_zpowers_d_le_pCoreOf h hJ h1523 hK3 hJY hJperf hJA5 hAJ hdA hdc
  have hcC : c ∈ commutatorInSubgroup J N :=
    mem_commutatorInSubgroup.mpr ⟨hcN, fun j hj =>
      (Subgroup.commutator_le.mp hcc) j hj c (Subgroup.mem_zpowers c)⟩
  have hdC : d ∈ commutatorInSubgroup J N :=
    mem_commutatorInSubgroup.mpr ⟨hdN, fun j hj =>
      (Subgroup.commutator_le.mp hdd) j hj d (Subgroup.mem_zpowers d)⟩
  have hbA : b ∈ A := mem_A_of_mem_pair hcA hdA hb
  have hbN : b ∈ Subgroup.normalizer (N : Set G) :=
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J) (hAJ hbA)
  have hbC : b ∈ commutatorInSubgroup J N := by
    rcases Set.mem_insert_iff.mp hb with hbc | hb2
    · rw [hbc]
      exact (commutatorInSubgroup J N).mul_mem hcC hdC
    · rw [Set.mem_singleton_iff.mp hb2]
      exact (commutatorInSubgroup J N).mul_mem hcC
        ((commutatorInSubgroup J N).pow_mem hdC 2)
  have hsub : Subgroup.zpowers b ≤ commutatorInSubgroup J N :=
    Subgroup.zpowers_le.mpr hbC
  exact Subgroup.commutator_le.mpr fun j hj k hk =>
    (mem_commutatorInSubgroup.mp (hsub hk)).2 j hj

theorem nonempty_residual_quot_a5 {J : Subgroup G} {b : G}
    (hJA5 : Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)))
    (hbJ : b ∈ Subgroup.normalizer (J : Set G)) (hb : Odd (orderOf b))
    (hJb : ⁅J, Subgroup.zpowers b⁆ ≤ CFSG.Open.pCoreOf 2 J) :
    Nonempty (↥(inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({b} : Set G))) ⧸
      CFSG.pCore 2 ↥(inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({b} : Set G))) ≃*
        alternatingGroup (Fin 5)) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := CFSG.Open.pCoreOf 2 J with hN
  set R : Subgroup G := Subgroup.zpowers b with hR
  set C : Subgroup G := J ⊓ Subgroup.centralizer ({b} : Set G) with hC
  have hNle : N ≤ J := CFSG.LieType.BorelTits.pCoreOf_le 2 J
  have hN2 : IsPGroup 2 N := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J
  have hJN : J ≤ Subgroup.normalizer (N : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J
  have hNnormal : (N.subgroupOf J).Normal := by
    rw [hN, CFSG.openPCoreOf_subgroupOf]
    exact CFSG.pCore_normal (p := 2) (G := ↥J)
  have hbN : b ∈ Subgroup.normalizer (N : Set G) :=
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J) hbJ
  have hRN : R ≤ Subgroup.normalizer (N : Set G) := Subgroup.zpowers_le.mpr hbN
  haveI : Group.IsNilpotent N := hN2.isNilpotent
  have hsolvN : Group.IsSolvable ↥N := inferInstance
  have hRodd : Odd (Nat.card R) := by
    rw [hR, Nat.card_zpowers]
    exact hb
  have hcop : Nat.Coprime (Nat.card N) (Nat.card R) := by
    obtain ⟨m, hm⟩ := hN2.exists_card_eq
    rw [hm]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hRodd)
  have hcommJb : ⁅J, R⁆ ≤ N := hJb
  have hcentR : Subgroup.centralizer (R : Set G) =
      Subgroup.centralizer ({b} : Set G) := by
    rw [hR, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hCN : C ⊔ N = J := by
    refine le_antisymm (sup_le inf_le_left hNle) ?_
    intro j hj
    obtain ⟨c, hcJ, hcR, hjcN⟩ :=
      CFSG.GroupTheory.exists_mem_centralizer_of_commutator_mem
        (X := J) (N := N) (R := R) hNle hNnormal hRN hsolvN hcop hj
        (fun r hr => (Subgroup.commutator_le.mp hcommJb) j hj r hr)
    have hcC : c ∈ C := by
      rw [hC]
      refine ⟨hcJ, ?_⟩
      have hmem : c ∈ Subgroup.centralizer (R : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        exact (hcR r hr).symm
      change c ∈ Subgroup.centralizer ({b} : Set G)
      rwa [← hcentR]
    have hcjN : c⁻¹ * j ∈ N := by
      have h := N.inv_mem hjcN
      rwa [mul_inv_rev, inv_inv] at h
    have hmem : j ∈ (C : Set G) * (N : Set G) :=
      ⟨c, hcC, c⁻¹ * j, hcjN, by group⟩
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right C N (inf_le_left.trans hJN)] at hmem
    exact hmem
  have hCNsub : C.subgroupOf J ⊔ CFSG.pCore 2 ↥J = ⊤ := by
    have h1 := Subgroup.subgroupOf_sup (A := C) (A' := N) (B := J) inf_le_left hNle
    rw [hCN, Subgroup.subgroupOf_self, hN, CFSG.openPCoreOf_subgroupOf] at h1
    exact h1.symm
  let NJ : Subgroup ↥J := CFSG.pCore 2 ↥J
  let QJ := ↥J ⧸ NJ
  let πJ : ↥J →* QJ := QuotientGroup.mk' NJ
  let CJ : Subgroup ↥J := C.subgroupOf J
  let RC : Subgroup ↥J := inSubgroup perfectResidual CJ
  have hQJperf : Group.IsPerfect QJ := by
    have hA5perf : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
    haveI : Group.IsPerfect (alternatingGroup (Fin 5)) := hA5perf
    obtain ⟨e⟩ := hJA5
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hCJtop : CJ.map πJ = ⊤ := by
    rw [← Subgroup.map_top_of_surjective πJ (QuotientGroup.mk'_surjective NJ)]
    rw [Subgroup.map_eq_map_iff]
    rw [show πJ.ker = NJ from QuotientGroup.ker_mk' NJ, hCNsub, top_sup_eq]
  have hmapRC : RC.map πJ = ⊤ := by
    rw [CFSG.RankThree.PartTwo.Sec14.Item148HJ.map_inSubgroup_perfectResidual πJ CJ,
      hCJtop]
    have htopPerf : Group.IsPerfect ↥(⊤ : Subgroup QJ) :=
      Group.IsPerfect.ofSurjective
        (f := (Subgroup.topEquiv (G := QJ)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := QJ)).symm.surjective
    exact inSubgroup_perfectResidual_of_isPerfect htopPerf
  have hpcQJ : CFSG.pCore 2 QJ = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (H := ↥J) (p := 2)
  let φ : ↥RC →* QJ := πJ.comp RC.subtype
  have hφsurj : Function.Surjective φ := by
    intro q
    have hq : q ∈ RC.map πJ := hmapRC ▸ Subgroup.mem_top q
    obtain ⟨r, hr, rfl⟩ := hq
    exact ⟨⟨r, hr⟩, rfl⟩
  have hφker2 : IsPGroup 2 φ.ker := by
    have hNJ2 : IsPGroup 2 NJ := CFSG.pCore_isPGroup (p := 2) (G := ↥J)
    have hkerEq : φ.ker = NJ.comap RC.subtype := by
      rw [show φ = πJ.comp RC.subtype from rfl, ← MonoidHom.comap_ker,
        QuotientGroup.ker_mk']
    rw [hkerEq]
    exact hNJ2.comap_of_injective RC.subtype RC.subtype_injective
  have hpcRC_le_ker : CFSG.pCore 2 ↥RC ≤ φ.ker := by
    have hmapnorm : ((CFSG.pCore 2 ↥RC).map φ).Normal :=
      Subgroup.Normal.map (CFSG.pCore_normal (p := 2) (G := ↥RC)) φ hφsurj
    have hmap2 : IsPGroup 2 ((CFSG.pCore 2 ↥RC).map φ) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥RC)).map φ
    have hle : (CFSG.pCore 2 ↥RC).map φ ≤ CFSG.pCore 2 QJ :=
      CFSG.LieType.BorelTits.le_pCore 2 hmapnorm hmap2
    rw [hpcQJ, le_bot_iff] at hle
    exact (Subgroup.map_eq_bot_iff (CFSG.pCore 2 ↥RC)).mp hle
  have hpcRC : CFSG.pCore 2 ↥RC = φ.ker :=
    le_antisymm hpcRC_le_ker
      (CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker φ) hφker2)
  let θ : ↥RC →* (QJ ⧸ CFSG.pCore 2 QJ) :=
    (QuotientGroup.mk' (CFSG.pCore 2 QJ)).comp φ
  have hθsurj : Function.Surjective θ :=
    (QuotientGroup.mk'_surjective _).comp hφsurj
  have hθker : θ.ker = CFSG.pCore 2 ↥RC := by
    rw [show θ = (QuotientGroup.mk' (CFSG.pCore 2 QJ)).comp φ from rfl,
      ← MonoidHom.comap_ker, QuotientGroup.ker_mk', hpcQJ, MonoidHom.comap_bot, hpcRC]
  have e1 : (↥RC ⧸ CFSG.pCore 2 ↥RC) ≃* (QJ ⧸ CFSG.pCore 2 QJ) :=
    (QuotientGroup.quotientMulEquivOfEq hθker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hθsurj)
  obtain ⟨eQ⟩ := hJA5
  have e2 : (QJ ⧸ CFSG.pCore 2 QJ) ≃* alternatingGroup (Fin 5) :=
    ((QuotientGroup.quotientMulEquivOfEq hpcQJ).trans
      (QuotientGroup.quotientBot (G := QJ))).trans eQ
  have eRC : (↥RC ⧸ CFSG.pCore 2 ↥RC) ≃* alternatingGroup (Fin 5) := e1.trans e2
  have hImap : RC.map J.subtype = inSubgroup perfectResidual C := by
    rw [CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective
      J.subtype J.subtype_injective CJ]
    rw [Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  let eI : ↥RC ≃* ↥(inSubgroup perfectResidual C) :=
    (Subgroup.equivMapOfInjective RC J.subtype J.subtype_injective).trans
      (MulEquiv.subgroupCongr hImap)
  have heI : (CFSG.pCore 2 ↥RC).map eI.toMonoidHom =
      CFSG.pCore 2 ↥(inSubgroup perfectResidual C) :=
    CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 eI
  have e3 : (↥RC ⧸ CFSG.pCore 2 ↥RC) ≃*
      (↥(inSubgroup perfectResidual C) ⧸
        CFSG.pCore 2 ↥(inSubgroup perfectResidual C)) :=
    QuotientGroup.congr (CFSG.pCore 2 ↥RC)
      (CFSG.pCore 2 ↥(inSubgroup perfectResidual C)) eI heI
  exact ⟨e3.symm.trans eRC⟩

theorem residual_facts
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    (h1523 : Item1523R) (hK3 : KFacts.KS166J2A5Three) {J : Subgroup G} (hJY : J ≤ Y₀)
    (hJperf : Group.IsPerfect ↥J)
    (hJA5 : Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)))
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) {d : G} (hdA : d ∈ A)
    (hdc : IsThreeCentralIn L d) {b : G} (hb : b ∈ ({c * d, c * d ^ 2} : Set G)) :
    Group.IsPerfect ↥(inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({b} : Set G))) ∧
      Nonempty (↥(inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({b} : Set G))) ⧸
        CFSG.pCore 2 ↥(inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({b} : Set G))) ≃*
          alternatingGroup (Fin 5)) ∧
      A ≤ Subgroup.normalizer
        ((inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({b} : Set G)) :
          Subgroup G) : Set G) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hbA : b ∈ A := mem_A_of_mem_pair hcA hdA hb
  have hbJ : b ∈ Subgroup.normalizer (J : Set G) := hAJ hbA
  have hb3 : b ^ 3 = 1 := h.toSec14Std.isE27.1.2 b hbA
  have hbodd : Odd (orderOf b) := by
    have hdvd : orderOf b ∣ 3 := orderOf_dvd_of_pow_eq_one hb3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · rw [h1]; norm_num
    · rw [h3]; norm_num
  have hJb : ⁅J, Subgroup.zpowers b⁆ ≤ CFSG.Open.pCoreOf 2 J :=
    commutator_zpowers_b_le_pCoreOf h hJ h1523 hK3 hJY hJperf hJA5 hAJ hdA hdc hb
  refine ⟨?_, ?_, ?_⟩
  · exact CFSG.RankThree.PartTwo.Sec6.isPerfect_inSubgroup_perfectResidual
      (J ⊓ Subgroup.centralizer ({b} : Set G))
  · exact nonempty_residual_quot_a5 hJA5 hbJ hbodd hJb
  · have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val
          (h.toSec13Data.isElemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨b, hbA⟩))
    refine (le_inf hAJ (hAb.trans Subgroup.le_normalizer)).trans ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf.trans
      (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
        (J ⊓ Subgroup.centralizer ({b} : Set G)))

end CFSG.RankThree.PartTwo.Sec16.Ctr166
