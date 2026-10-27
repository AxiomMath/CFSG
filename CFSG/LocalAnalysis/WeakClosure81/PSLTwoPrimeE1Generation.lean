module

public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate43

import CFSG.GroupTheory.InvertedTorusCoset
import CFSG.GroupTheory.SylowCover
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.CGT.PushingUpLit.SolKAb.CyclicTI
import CFSG.LocalAnalysis.ComponentClassification.FooteLitElemAb
import CFSG.Quasithin.Background.E1Invariance
import CFSG.Quasithin.Background.E1Sec6
import CFSG.Quasithin.Background.E1Solv
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2KleinFourCentralizerEqSelf
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectOfCard
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.PSL2ReflectedTorusCard
import CFSG.Dihedral.PerfectDihedralFourgroupAction
import CFSG.Quasithin.EmptyFaithful.E22PD1
import CFSG.Quasithin.EmptyFaithful.E22PS4
import CFSG.Quasithin.EmptyFaithful.E22PTor
import CFSG.Quasithin.EmptyFaithful.E22PL2Sev
import CFSG.Quasithin.EmptyFaithful.E22PL2PglC
import CFSG.GH74.Generic.BProg.B2.GenLocPsl2Full
import CFSG.GroupTheory.SolvableTransport
import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
import CFSG.CGT.PushingUpLit.SolKAb.Setup
import CFSG.Quasithin.Vol2.Ch11SecU1L3IN
import CFSG.CharacterTheory.Semidihedral.ParameterFiveGeneration
import CFSG.LocalAnalysis.WeakClosure81.TenFive
import CFSG.Walter.PSL2Facts.Odd
import CFSG.Walter.Bender1970.S3.Tools
public import CFSG.Assembly.QuasithinDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.Basic
import CFSG.Foundations
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.Quasithin.Background.G11Basic
import CFSG.Quasithin.EmptyFaithful.E22PGen
import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunction
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CoprimeActionNontrivialTransfer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2S0LeQuotientTorus
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character
import CFSG.Walter.Bender1970.S2
import CFSG.Walter.Bender1970.S3.Basic
import CFSG.Walter.PSL2Facts
import Certificates.Certificate10
import Certificates.Certificate100
import Certificates.Certificate101
import Certificates.Certificate102
import Certificates.Certificate103
import Certificates.Certificate104
import Certificates.Certificate105
import Certificates.Certificate106
import Certificates.Certificate107
import Certificates.Certificate108
import Certificates.Certificate109
import Certificates.Certificate11
import Certificates.Certificate12
import Certificates.Certificate3
import Certificates.Certificate4
import Certificates.Certificate42
import Certificates.Certificate44
import Certificates.Certificate5
import Certificates.Certificate6
import Certificates.Certificate7
import Certificates.Certificate8
import Certificates.Certificate9
import Certificates.Certificate96
import Certificates.Certificate97
import Certificates.Certificate98
import Certificates.Certificate99

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.E22L2 CFSG.GorensteinWalter
open scoped Pointwise commutatorElement
open CFSG.CGT.PushingUpLit.SolKAb (forall_mul_comm_of_isCyclic)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]

private theorem exists_isKleinFour_mem_notMem_zpowers {G : Type*} [Group G]
    {B : Subgroup G} (hB : IsKleinFour ↥B) {z : G} (hzB : z ∈ B) (hz2 : orderOf z = 2) :
    ∃ b ∈ B, b ∉ Subgroup.zpowers z ∧ b ^ 2 = 1 ∧ b ≠ 1 := by
  classical
  have hB4 : Nat.card ↥B = 4 := IsKleinFour.card_four
  have hbexists : ∃ b ∈ B, b ∉ Subgroup.zpowers z := by
    by_contra h
    push Not at h
    have hEq : B = Subgroup.zpowers z :=
      le_antisymm (fun x hx => h x hx) (Subgroup.zpowers_le.mpr hzB)
    have hcard : Nat.card ↥B = Nat.card ↥(Subgroup.zpowers z) := by rw [hEq]
    rw [Nat.card_zpowers, hz2, hB4] at hcard
    omega
  obtain ⟨b, hbB, hbz⟩ := hbexists
  exact ⟨b, hbB, hbz, CFSG.ComponentClassification.FooteLit.sq_eq_one_of_isKleinFour hB hbB,
    fun h => hbz (h.symm ▸ Subgroup.one_mem _)⟩

omit [Fact (Nat.Prime p)] in
private theorem torus_le_genEi
    {S B U : Subgroup (PSL2 K)} (hS : Quasithin.IsSylowIn 2 S ⊤) (hBS : B ≤ S)
    (hBab : IsElemAbelian 2 B) (hB4 : Nat.card ↥B = 4)
    {z b : PSL2 K} (hzB : z ∈ B) (hz2 : orderOf z = 2) (hzU : z ∈ U)
    (hbB : b ∈ B) (hbInv : ∀ x ∈ U, b * x * b⁻¹ = x⁻¹)
    (hUc : IsCyclic ↥U)
    (hUC : U ≤ Subgroup.centralizer ({z} : Set (PSL2 K)))
    (hDN : ∀ P : Subgroup (PSL2 K), P ≤ U →
      Subgroup.centralizer ({z} : Set (PSL2 K)) ≤ Subgroup.normalizer (P : Set (PSL2 K)))
    (hSylD : Quasithin.IsSylowIn 2 S (Subgroup.centralizer ({z} : Set (PSL2 K)))) :
    U ≤ S ⊔ (⨆ I ∈ {I : Subgroup (PSL2 K) |
      IsE 1 ⊤ S B I ∧ EOne ↥I (B.subgroupOf I)}, I) := by
  have hSD : S ≤ Subgroup.centralizer ({z} : Set (PSL2 K)) := hSylD.le
  have hUcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := forall_mul_comm_of_isCyclic hUc
  have hsup : ((⨆ r ∈ (Nat.card ↥U).primeFactors,
      ((default : Sylow r ↥U) : Subgroup ↥U)) : Subgroup ↥U).map U.subtype = U := by
    rw [Sylow.iSup_sylow_eq_top (G := ↥U), ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hsup]
  simp_rw [Subgroup.map_iSup]
  refine iSup₂_le ?_
  intro r hr
  set P : Subgroup (PSL2 K) := ((default : Sylow r ↥U) : Subgroup ↥U).map U.subtype with hP
  have hrprime : r.Prime := Nat.prime_of_mem_primeFactors hr
  have : Fact r.Prime := ⟨hrprime⟩
  have hPU : P ≤ U := by
    rw [hP]
    exact Subgroup.map_subtype_le _
  have hPr : IsPGroup r P := by
    rw [hP]
    exact (default : Sylow r ↥U).isPGroup'.map U.subtype
  have hQne : ((default : Sylow r ↥U) : Subgroup ↥U) ≠ ⊥ :=
    (default : Sylow r ↥U).ne_bot_of_dvd_card (Nat.dvd_of_mem_primeFactors hr)
  have hPne : P ≠ ⊥ := by
    rw [hP]
    intro hbot
    exact hQne ((Subgroup.map_eq_bot_iff_of_injective _ U.subtype_injective).mp hbot)
  by_cases hr2 : r = 2
  · subst hr2
    have hPD : P ≤ Subgroup.centralizer ({z} : Set (PSL2 K)) := hPU.trans hUC
    have hPnorm : (P.subgroupOf (Subgroup.centralizer ({z} : Set (PSL2 K)))).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (hDN P hPU)
    exact (hSylD.le_of_normal hPD hPnorm hPr).trans le_sup_left
  · have hPodd : Odd (Nat.card ↥P) := by
      obtain ⟨n, hn⟩ := hPr.exists_card_eq
      rw [hn]
      exact Odd.pow (hrprime.odd_of_ne_two hr2)
    have hBN : B ≤ Subgroup.normalizer (P : Set (PSL2 K)) :=
      hBS.trans (hSD.trans (hDN P hPU))
    have hbN : b ∈ Subgroup.normalizer (P : Set (PSL2 K)) :=
      hDN P hPU (hSD (hBS hbB))
    have hbInvP : ∀ x ∈ P, b * x * b⁻¹ = x⁻¹ := fun x hx => hbInv x (hPU hx)
    have hcomm_b : ⁅P, Subgroup.zpowers b⁆ = P :=
      CFSG.Walter.commutator_zpowers_eq_self_of_conj_eq_inv hbN hbInvP hPodd
    have hcomm_le : ⁅P, B⁆ ≤ P := E1.commutator_le_of_le_normalizer hBN
    have hcomm_ge : P ≤ ⁅P, B⁆ :=
      hcomm_b.ge.trans (Subgroup.commutator_mono_right (Subgroup.zpowers_le.mpr hbB))
    have hcomm : ⁅P, B⁆ = P := le_antisymm hcomm_le hcomm_ge
    have hHzB : Subgroup.zpowers z ≤ B := Subgroup.zpowers_le.mpr hzB
    have hHzcentral : Subgroup.zpowers z ≤ Subgroup.centralizer (P : Set (PSL2 K)) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hUcomm z hzU y (hPU hy)).symm
    have hHzindex : (Subgroup.zpowers z).relIndex B ≤ 2 := by
      have hidx := Subgroup.relIndex_mul_card (H := Subgroup.zpowers z) (K := B)
      rw [inf_eq_left.mpr hHzB, Nat.card_zpowers, hz2, hB4] at hidx
      omega
    have hτP : tauOf ⊤ S B ≤ Subgroup.normalizer (P : Set (PSL2 K)) :=
      (E1.tauOf_le ⊤ S B).trans (hSD.trans (hDN P hPU))
    obtain ⟨hIsE, hEOne, -⟩ := E1.isE_one_sup hrprime hr2 hS hBS hBab hPr hPne
      hτP hcomm hHzB hHzcentral hHzindex
    have hmem : P ⊔ tauOf ⊤ S B ≤ S ⊔ (⨆ I ∈ {I : Subgroup (PSL2 K) |
        IsE 1 ⊤ S B I ∧ EOne ↥I (B.subgroupOf I)}, I) :=
      (le_iSup₂_of_le (f := fun I (_ : IsE 1 ⊤ S B I ∧ EOne ↥I (B.subgroupOf I)) => I)
        (P ⊔ tauOf ⊤ S B) ⟨hIsE, hEOne⟩ le_rfl).trans le_sup_right
    exact le_sup_left.trans hmem

private theorem exists_inverting_mem_of_isKleinFour
    {B U : Subgroup (PSL2 K)} (hB : IsKleinFour ↥B) {z w : PSL2 K}
    (hzB : z ∈ B) (hz2 : orderOf z = 2) (hUc : IsCyclic ↥U) (hzU : z ∈ U)
    (hww : w * w = 1) (hwinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹)
    (hC : Subgroup.centralizer ({z} : Set (PSL2 K)) = U ⊔ Subgroup.zpowers w)
    (hBC : B ≤ Subgroup.centralizer ({z} : Set (PSL2 K))) :
    ∃ b ∈ B, b ∉ U ∧ ∃ u ∈ U, b = u * w ∧ ∀ x ∈ U, b * x * b⁻¹ = x⁻¹ := by
  obtain ⟨b, hbB, hbz, hb2, hb1⟩ := exists_isKleinFour_mem_notMem_zpowers hB hzB hz2
  have hzI := CFSG.Semidihedral.ParameterFive.isInvolution_of_orderOf_eq_two hz2
  have hbU : b ∉ U := by
    intro hbU'
    have hzb : z = b := e22pl2pgl_involution_unique hUc hzU hbU' hzI.2 hb2 hzI.1 hb1
    exact hbz (by rw [← hzb]; exact Subgroup.mem_zpowers z)
  have hbUsup : b ∈ U ⊔ Subgroup.zpowers w := by
    rw [← hC]
    exact hBC hbB
  obtain ⟨u, huU, hb_eq⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecU1.L3I.eq_mul_of_mem_sup_zpowers hww hwinv hbUsup hbU
  refine ⟨b, hbB, hbU, u, huU, hb_eq, ?_⟩
  exact CFSG.Quasithin.Vol2.Ch11.SecU1.L3I.inverts_of_mem_sup_zpowers
    (forall_mul_comm_of_isCyclic hUc) hww hwinv hbUsup hbU

omit [Fact (Nat.Prime p)] in
private theorem centralizer_le_genEi
    (hodd : IsOddPrimePower (Nat.card K))
    {S B : Subgroup (PSL2 K)} (hS : Quasithin.IsSylowIn 2 S ⊤) (hBS : B ≤ S)
    (hB : IsKleinFour ↥B) (hBab : IsElemAbelian 2 B) {z : PSL2 K} (hzB : z ∈ B)
    (hz2 : orderOf z = 2) (hzc : ∀ t ∈ S, z * t = t * z) :
    Subgroup.centralizer ({z} : Set (PSL2 K)) ≤
      S ⊔ (⨆ I ∈ {I : Subgroup (PSL2 K) |
        IsE 1 ⊤ S B I ∧ EOne ↥I (B.subgroupOf I)}, I) := by
  classical
  have hB4 : Nat.card ↥B = 4 := IsKleinFour.card_four
  have hzI := CFSG.Semidihedral.ParameterFive.isInvolution_of_orderOf_eq_two hz2
  obtain ⟨U, w, hUc, hzU, hwI, -, hwinv, hC, -, -⟩ :=
    psl2_reflected_torus_card hodd hzI
  have hww : w * w = 1 := by simpa [pow_two] using hwI.2
  have hSD : S ≤ Subgroup.centralizer ({z} : Set (PSL2 K)) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact hzc t ht
  have hSylD : Quasithin.IsSylowIn 2 S (Subgroup.centralizer ({z} : Set (PSL2 K))) :=
    ⟨hSD, hS.isPGroup, fun hd => hS.not_dvd_relIndex (by
      simpa [Subgroup.relIndex_top_right] using
        hd.trans (Subgroup.relIndex_dvd_index_of_le hSD))⟩
  obtain ⟨b, hbB, hbU, u, huU, hb_eq, hbInv⟩ :=
    exists_inverting_mem_of_isKleinFour hB hzB hz2 hUc hzU hww hwinv hC (hBS.trans hSD)
  have hDN : ∀ P : Subgroup (PSL2 K), P ≤ U →
      Subgroup.centralizer ({z} : Set (PSL2 K)) ≤ Subgroup.normalizer (P : Set (PSL2 K)) :=
    fun P hPU => by
      rw [hC]
      exact CFSG.GroupTheory.sup_zpowers_le_normalizer_of_inverting
        (forall_mul_comm_of_isCyclic hUc) hww hwinv hPU
  have hUC : U ≤ Subgroup.centralizer ({z} : Set (PSL2 K)) := by
    rw [hC]
    exact le_sup_left
  have hUleM := torus_le_genEi hS hBS hBab hB4 hzB hz2 hzU hbB hbInv hUc hUC hDN hSylD
  have hwM : w ∈ S ⊔ (⨆ I ∈ {I : Subgroup (PSL2 K) |
      IsE 1 ⊤ S B I ∧ EOne ↥I (B.subgroupOf I)}, I) := by
    have huM : u ∈ S ⊔ (⨆ I ∈ {I : Subgroup (PSL2 K) |
        IsE 1 ⊤ S B I ∧ EOne ↥I (B.subgroupOf I)}, I) := hUleM huU
    have hbM : b ∈ S ⊔ (⨆ I ∈ {I : Subgroup (PSL2 K) |
        IsE 1 ⊤ S B I ∧ EOne ↥I (B.subgroupOf I)}, I) :=
      Subgroup.mem_sup_left (hBS hbB)
    have hw_eq : w = u⁻¹ * b := by
      rw [hb_eq]
      group
    rw [hw_eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ huM) hbM
  have hDle : Subgroup.centralizer ({z} : Set (PSL2 K)) ≤
      S ⊔ (⨆ I ∈ {I : Subgroup (PSL2 K) |
        IsE 1 ⊤ S B I ∧ EOne ↥I (B.subgroupOf I)}, I) := by
    rw [hC]
    exact sup_le hUleM (Subgroup.zpowers_le.mpr hwM)
  exact hDle

omit [Fact (Nat.Prime p)] in
private theorem exists_odd_prime_dvd_card_of_isSylow_card_four
    (hK : Nat.card K = p) (hp : 11 ≤ p) {S U : Subgroup (PSL2 K)}
    (hS : Quasithin.IsSylowIn 2 S ⊤) (hS4 : Nat.card S = 4)
    (hcard : Nat.card U = (Nat.card K - 1) / 2 ∨ Nat.card U = (Nat.card K + 1) / 2) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card U := by
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (Nat.card U) with
    ⟨k, hk⟩ | ⟨r, hr, hrdvd, hrodd⟩
  · exfalso
    have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := k) hk
    obtain ⟨Ss, hST⟩ := hS.exists_sylow_eq_of_top
    obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hU2
    have hQcard : Nat.card ↥Q = Nat.card S := by
      rw [← hST]
      exact Nat.card_congr (Sylow.equiv Q Ss).toEquiv
    have hle : Nat.card U ≤ Nat.card S :=
      (Subgroup.card_le_of_le hQ).trans (le_of_eq hQcard)
    have hge : 5 ≤ Nat.card U := by
      rcases hcard with h | h
      · rw [h, hK]; omega
      · rw [h, hK]; omega
    omega
  · exact ⟨r, hr, by obtain ⟨k, hk⟩ := hrodd; omega, hrdvd⟩

private theorem exists_member_not_le_centralizer_dihedral
    (hcard3 : 3 < Nat.card K) (hodd : IsOddPrimePower (Nat.card K))
    {S B : Subgroup (PSL2 K)} (hS : Quasithin.IsSylowIn 2 S ⊤) (hBS : B ≤ S)
    (hB : IsKleinFour ↥B) (hO2 : pCoreOf 2 (⊤ : Subgroup (PSL2 K)) = ⊥)
    {m : ℕ} (hm2 : 2 ≤ m) (e : ↥S ≃* DihedralGroup (2 ^ m)) {z : PSL2 K}
    (hz2 : orderOf z = 2)
    (hzV : ∀ V : Subgroup (PSL2 K), V ≤ S → IsKleinFour ↥V → z ∈ V) :
    ∃ I : Subgroup (PSL2 K), IsE 1 ⊤ S B I ∧ EOne ↥I (B.subgroupOf I) ∧
      ¬ I ≤ Subgroup.centralizer ({z} : Set (PSL2 K)) := by
  classical
  have : Group.IsPerfect (PSL2 K) := psl2_isPerfect_of_card_gt_three K hcard3
  obtain ⟨V', hV'T, hV', hne, hV'N, hVN, hN8, hC', hcomm'⟩ :=
    dihedral_kleinFour_partner hm2 e hBS hB
  have hcent : Subgroup.centralizer (V' : Set (PSL2 K)) = V' :=
    psl2_kleinFour_centralizer_eq_self K hodd V' hV'
  obtain ⟨Ss, hST⟩ := hS.exists_sylow_eq_of_top
  have eSs : ↥Ss ≃* DihedralGroup (2 ^ m) := (MulEquiv.subgroupCongr hST).trans e
  have hsurj : Function.Surjective V'.normalizerMonoidHom :=
    perfect_dihedral_fourgroup_normalizer_surjective Ss hm2 eSs V'
      (hST.symm ▸ hV'T) hV'
  have hIsE : IsE 1 ⊤ S B (Subgroup.normalizer (V' : Set (PSL2 K))) :=
    isE_one_normalizer_kleinFour hS hO2 hB hV' hBS hV'T hne hcent hsurj hN8 hVN hC' hcomm'
  have hNsolv : Group.IsSolvable ↥(Subgroup.normalizer (V' : Set (PSL2 K))) :=
    (e22pl2s_normalizer_pCore_solvable hV' hcent hsurj).2
  have hEOne : EOne ↥(Subgroup.normalizer (V' : Set (PSL2 K)))
      (B.subgroupOf (Subgroup.normalizer (V' : Set (PSL2 K)))) :=
    (E1.isE_eOne_of_isSolvable hIsE hNsolv).1
  exact ⟨Subgroup.normalizer (V' : Set (PSL2 K)), hIsE, hEOne,
    not_normalizer_le_centralizer hV' hsurj (hzV V' hV'T hV') (by
      simpa using (CFSG.Semidihedral.ParameterFive.isInvolution_of_orderOf_eq_two hz2).1)⟩

private theorem exists_inverting_of_centralizer_torus
    {Ub : Subgroup (PSL2 K)} {b wb z : PSL2 K} (hUbc : IsCyclic ↥Ub)
    (hbUb : b ∈ Ub) (hwbw : wb * wb = 1) (hwbInv : ∀ x ∈ Ub, wb * x * wb⁻¹ = x⁻¹)
    (hCb : Subgroup.centralizer ({b} : Set (PSL2 K)) = Ub ⊔ Subgroup.zpowers wb)
    (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1) (hbz_z : b ≠ z)
    (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    (hzCb : z ∈ Subgroup.centralizer ({b} : Set (PSL2 K))) :
    ∃ v ∈ Ub, z = v * wb ∧ ∀ x ∈ Ub, z * x * z⁻¹ = x⁻¹ := by
  have hzUb : z ∉ Ub := by
    intro hzUb'
    exact hbz_z (e22pl2pgl_involution_unique hUbc hbUb hzUb' hb2 hz2 hb1 hz1)
  have hzUbsup : z ∈ Ub ⊔ Subgroup.zpowers wb := by
    rw [← hCb]
    exact hzCb
  obtain ⟨v, hvUb, hz_eq⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecU1.L3I.eq_mul_of_mem_sup_zpowers hwbw hwbInv hzUbsup hzUb
  exact ⟨v, hvUb, hz_eq,
    CFSG.Quasithin.Vol2.Ch11.SecU1.L3I.inverts_of_mem_sup_zpowers
      (forall_mul_comm_of_isCyclic hUbc) hwbw hwbInv hzUbsup hzUb⟩

private theorem isKleinFour_le_normalizer_of_inverting
    {B Ub : Subgroup (PSL2 K)} {b z : PSL2 K} (hB4 : Nat.card ↥B = 4)
    (hbB : b ∈ B) (hzB : z ∈ B) (hb1 : b ≠ 1) (hzb_z : z ∉ Subgroup.zpowers b)
    (hUbc : IsCyclic ↥Ub) (hz2 : z ^ 2 = 1)
    (hzInvUb : ∀ x ∈ Ub, z * x * z⁻¹ = x⁻¹)
    (hbUb_comm : ∀ x ∈ Ub, b * x = x * b) :
    B ≤ Subgroup.normalizer (Ub : Set (PSL2 K)) := by
  have hzN : z ∈ Subgroup.normalizer (Ub : Set (PSL2 K)) :=
    (CFSG.GroupTheory.sup_zpowers_le_normalizer_of_inverting
      (forall_mul_comm_of_isCyclic hUbc) (by simpa [pow_two] using hz2) hzInvUb le_rfl)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hbN : b ∈ Subgroup.normalizer (Ub : Set (PSL2 K)) :=
    Subgroup.centralizer_le_normalizer (Ub : Set (PSL2 K))
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hbUb_comm y hy).symm)
  intro x hx
  rcases e22ptor_mem_four hB4 hbB hzB hb1 hzb_z hx with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact hzN
  · exact hbN
  · exact Subgroup.mul_mem _ hzN hbN

omit [Fact (Nat.Prime p)] in
private theorem exists_member_not_le_centralizer_card_four
    (hK : Nat.card K = p) (hp : 11 ≤ p) (hodd : IsOddPrimePower (Nat.card K))
    {S B : Subgroup (PSL2 K)} (hS : Quasithin.IsSylowIn 2 S ⊤) (hBS : B ≤ S)
    (hB : IsKleinFour ↥B) (hBab : IsElemAbelian 2 B) {m : ℕ} (hm : m = 1)
    (e : ↥S ≃* DihedralGroup (2 ^ m)) {z : PSL2 K} (hzB : z ∈ B)
    (hz2 : orderOf z = 2) (hzc : ∀ t ∈ S, z * t = t * z) :
    ∃ I : Subgroup (PSL2 K), IsE 1 ⊤ S B I ∧ EOne ↥I (B.subgroupOf I) ∧
      ¬ I ≤ Subgroup.centralizer ({z} : Set (PSL2 K)) := by
  classical
  have hB4 : Nat.card ↥B = 4 := IsKleinFour.card_four
  have hS4 : Nat.card S = 4 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hm]
    norm_num
  have hSB : S = B :=
    (Subgroup.eq_of_le_of_card_ge hBS (by rw [hS4, hB4])).symm
  have hzI := CFSG.Semidihedral.ParameterFive.isInvolution_of_orderOf_eq_two hz2
  obtain ⟨b, hbB, hbz, hb2, hb1⟩ := exists_isKleinFour_mem_notMem_zpowers hB hzB hz2
  have hb2' : orderOf b = 2 := orderOf_eq_prime hb2 hb1
  have hbz_z : b ≠ z := fun h => hbz (h ▸ Subgroup.mem_zpowers z)
  have hcomm_zb : z * b = b * z := hzc b (hSB.symm ▸ hbB)
  have hbI : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution b := ⟨hb1, hb2⟩
  obtain ⟨Ub, wb, hUbc, hbUb, hwbI, -, hwbInv, hCb, -, hcardalt⟩ :=
    psl2_reflected_torus_card hodd hbI
  have hwbw : wb * wb = 1 := by simpa [pow_two] using hwbI.2
  have hzCb : z ∈ Subgroup.centralizer ({b} : Set (PSL2 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm_zb
  obtain ⟨-, -, hz_eq, hzInvUb⟩ :=
    exists_inverting_of_centralizer_torus hUbc hbUb hwbw hwbInv hCb hb2 hb1 hbz_z
      hzI.2 hzI.1 hzCb
  have hbUb_comm : ∀ x ∈ Ub, b * x = x * b := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer ({b} : Set (PSL2 K)) := by
      rw [hCb]
      exact Subgroup.mem_sup_left hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hxC
    exact hxC.symm
  have hzb_z : z ∉ Subgroup.zpowers b := by
    intro hzpb
    rcases e22pl2pgl_mem_zpowers_involution (by simpa [pow_two] using hb2) hzpb with h | h
    · exact hzI.1 h
    · exact hbz (h ▸ Subgroup.mem_zpowers z)
  have hBN : B ≤ Subgroup.normalizer (Ub : Set (PSL2 K)) :=
    isKleinFour_le_normalizer_of_inverting hB4 hbB hzB hb1 hzb_z hUbc hzI.2 hzInvUb hbUb_comm
  have hτUb : tauOf ⊤ S B ≤ Subgroup.normalizer (Ub : Set (PSL2 K)) := by
    rw [hSB]
    exact (E1.tauOf_le ⊤ B B).trans hBN
  obtain ⟨r, hr, hr2, hrUb⟩ :=
    exists_odd_prime_dvd_card_of_isSylow_card_four hK hp hS hS4 hcardalt
  obtain ⟨P₀, hP₀Ub, hP₀ne, hP₀grp, hIsE, hP₀notCz⟩ :=
    isE_one_of_odd_torus hS hBS hBab hB4 hbB hzB hb2' hzb_z hUbc hbUb_comm hzInvUb hτUb
      hr hr2 hrUb
  have hUbτsolv : Group.IsSolvable ↥(Ub ⊔ tauOf ⊤ S B) :=
    CFSG.GroupTheory.isSolvable_sup_of_isPGroup_of_le_normalizer
      (Group.isSolvable_of_comm fun x y => Subtype.ext
        (forall_mul_comm_of_isCyclic hUbc x x.2 y y.2))
      (hS.isPGroup.to_le (E1.tauOf_le ⊤ S B)) hτUb
  have : Group.IsSolvable ↥(Ub ⊔ tauOf ⊤ S B) := hUbτsolv
  have hP₀le : P₀ ⊔ tauOf ⊤ S B ≤ Ub ⊔ tauOf ⊤ S B :=
    sup_le (hP₀Ub.trans le_sup_left) le_sup_right
  have : Group.IsSolvable ↥((P₀ ⊔ tauOf ⊤ S B).subgroupOf (Ub ⊔ tauOf ⊤ S B)) :=
    inferInstance
  have hsolv : Group.IsSolvable ↥(P₀ ⊔ tauOf ⊤ S B) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hP₀le).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hP₀le).symm.injective
  have hEOne : EOne ↥(P₀ ⊔ tauOf ⊤ S B) (B.subgroupOf (P₀ ⊔ tauOf ⊤ S B)) :=
    (E1.isE_eOne_of_isSolvable hIsE hsolv).1
  exact ⟨P₀ ⊔ tauOf ⊤ S B, hIsE, hEOne,
    fun hle => hP₀notCz (le_trans le_sup_left hle)⟩

omit [Fact (Nat.Prime p)] in
private theorem pCoreOf_top_eq_bot_of_psl2 (hK : Nat.card K = p) (hp : 11 ≤ p) :
    pCoreOf 2 (⊤ : Subgroup (PSL2 K)) = ⊥ := by
  have : IsSimpleGroup (PSL2 K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hK]; omega)
  have hpc : CFSG.pCore 2 (PSL2 K) = ⊥ :=
    CFSG.CGT.PushingUpLit.SolKAb.pCore_two_eq_bot_of_simple_of_nonabelian
      CFSG.ABGLocalTools.psl2_exists_not_commute
  rw [CFSG.Quasithin.E1.pCoreOf_top_eq 2 (PSL2 K)]
  exact hpc

private theorem exists_dihedral_sylow_data (hodd : IsOddPrimePower (Nat.card K))
    {S : Subgroup (PSL2 K)} (hS : Quasithin.IsSylowIn 2 S ⊤) :
    ∃ (m : ℕ) (_ : ↥S ≃* DihedralGroup (2 ^ m)), 1 ≤ m := by
  obtain ⟨Ss, hST⟩ := hS.exists_sylow_eq_of_top
  obtain ⟨m, hm1, ⟨eSs⟩⟩ := psl2_odd_hasDihedralSylowTwo_model K hodd Ss
  exact ⟨m, (MulEquiv.subgroupCongr hST).symm.trans eSs, hm1⟩

private theorem isCoatom_centralizer_involution_psl2
    (hK : Nat.card K = p) (hp : 11 ≤ p) {z : PSL2 K} (hz2 : orderOf z = 2) :
    IsCoatom (Subgroup.centralizer ({z} : Set (PSL2 K))) :=
  CFSG.GH74.Generic.BProg.B2.psl2_isCoatom_centralizer_involution
    (p := p) (f := 1) (by rw [hK, pow_one]) (by omega) (by simpa using hp) hz2

theorem psl2_prime_sup_isE_one_and_eOne_eq_top
    {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p) (hp : 11 ≤ p)
    {S B : Subgroup (PSL2 K)}
    (hS : Quasithin.IsSylowIn 2 S ⊤) (hBS : B ≤ S)
    (hB : IsKleinFour ↥B) :
    S ⊔ (⨆ I ∈ {I : Subgroup (PSL2 K) |
      IsE 1 ⊤ S B I ∧ EOne ↥I (B.subgroupOf I)}, I) = ⊤ := by
  classical
  let M : Subgroup (PSL2 K) :=
    S ⊔ (⨆ I ∈ {I : Subgroup (PSL2 K) |
      IsE 1 ⊤ S B I ∧ EOne ↥I (B.subgroupOf I)}, I)
  change M = ⊤
  have hp2 : p ≠ 2 := by omega
  have hcard3 : 3 < Nat.card K := by rw [hK]; omega
  have hodd : IsOddPrimePower (Nat.card K) :=
    CFSG.Walter.isOddPrimePower_of_card (p := p) (f := 1) (by rw [hK, pow_one])
      ((Fact.out : p.Prime).odd_of_ne_two hp2) (by norm_num : 0 < 1)
  have hB4 : Nat.card ↥B = 4 := IsKleinFour.card_four
  have hBab : IsElemAbelian 2 B := ⟨IsKleinFour.isMulCommutative,
    fun _ hx => CFSG.ComponentClassification.FooteLit.sq_eq_one_of_isKleinFour hB hx⟩
  have hO2 : pCoreOf 2 (⊤ : Subgroup (PSL2 K)) = ⊥ := pCoreOf_top_eq_bot_of_psl2 hK hp
  obtain ⟨m, e, hm1⟩ := exists_dihedral_sylow_data hodd hS
  have finish : ∀ {z : PSL2 K} {I : Subgroup (PSL2 K)}, orderOf z = 2 →
      Subgroup.centralizer ({z} : Set (PSL2 K)) ≤ M → IsE 1 ⊤ S B I →
      EOne ↥I (B.subgroupOf I) → ¬ I ≤ Subgroup.centralizer ({z} : Set (PSL2 K)) →
      M = ⊤ := by
    intro z I hz hDle hIsE hEOne hnotI
    have hIM : I ≤ M :=
      (le_iSup₂_of_le (f := fun J (_ : IsE 1 ⊤ S B J ∧ EOne ↥J (B.subgroupOf J)) => J)
        I ⟨hIsE, hEOne⟩ le_rfl).trans le_sup_right
    have hlt : Subgroup.centralizer ({z} : Set (PSL2 K)) < M := by
      refine lt_of_le_of_ne hDle ?_
      intro h
      exact hnotI (h ▸ hIM)
    exact (isCoatom_centralizer_involution_psl2 hK hp hz).2 M hlt
  by_cases hm : m = 1
  ·
    have hS4 : Nat.card S = 4 := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hm]
      norm_num
    have hSB : S = B :=
      (Subgroup.eq_of_le_of_card_ge hBS (by rw [hS4, hB4])).symm
    obtain ⟨zB, hzB'⟩ :=
      exists_prime_orderOf_dvd_card' 2 (G := ↥B) (by rw [hB4]; norm_num)
    let z : PSL2 K := (zB : PSL2 K)
    have hzB : z ∈ B := zB.2
    have hz2 : orderOf z = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hzB'
    have hzc : ∀ t ∈ S, z * t = t * z := by
      intro t ht
      rw [hSB] at ht
      exact hBab.comm hzB ht
    have hDle : Subgroup.centralizer ({z} : Set (PSL2 K)) ≤ M :=
      centralizer_le_genEi hodd hS hBS hB hBab hzB hz2 hzc
    obtain ⟨I, hIsE, hEOne, hnotI⟩ :=
      exists_member_not_le_centralizer_card_four hK hp hodd hS hBS hB hBab hm e hzB hz2 hzc
    exact finish hz2 hDle hIsE hEOne hnotI
  ·
    have hm2 : 2 ≤ m := by omega
    obtain ⟨z, -, hz2, hzc, hzV, -⟩ := dihedral_sylow_data hm2 e
    have hzB : z ∈ B := hzV B hBS hB
    have hDle : Subgroup.centralizer ({z} : Set (PSL2 K)) ≤ M :=
      centralizer_le_genEi hodd hS hBS hB hBab hzB hz2 hzc
    obtain ⟨I, hIsE, hEOne, hnotI⟩ :=
      exists_member_not_le_centralizer_dihedral hcard3 hodd hS hBS hB hO2 hm2 e hz2 hzV
    exact finish hz2 hDle hIsE hEOne hnotI

end CFSG.LocalAnalysis.WeakClosure81
