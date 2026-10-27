module

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFixedEnd

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCExcluded3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.Carrier
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFixedRank
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SylowThreeAxisNormalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKernel
public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107E3Norm
import CFSG.GroupTheory.CoprimeCentralizerRank
import CFSG.GroupTheory.CommutingProductFixedSubgroup
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
import CFSG.LocalAnalysis.StronglyEmbedded.OfCentralizers
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorSupLeOfCommutatorLeAndNormalize
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 calC)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.Yardstones.Mf4cdcdf2e013 (Asc83CComponent)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3

theorem pRank_L_eq_three_of_isSCPrime (c : Ctx82E3 D) {p : ℕ} (hSC : c.IsSCPrime p) :
    CFSG.Open.pRank p c.L = 3 := by
  have hp := (D.sig_prime p hSC.1).1
  have hm := c.pRank_eq_three_of_mem_sigma hSC.1
  have hl := Theorem82.pRank_le_of_not_dvd_index hp c.hyp81.1 hSC.2
  have hu := (CFSG.SectionRank.pRank_mono hp.one_lt c.hyp81.1).trans
    (c.pRank_le_three hp (D.sig_prime p hSC.1).2)
  omega

theorem pRank_Lf_eq_one_of_isSCPrime (c : Ctx82E3 D) (X : C4Data G D.M)
    {p : ℕ} (hSC : c.IsSCPrime p)
    (d : SylowThreeData G) (hdM : d.M = D.M) (hdL : d.L = c.L) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) (hdS : d.S = P ⊓ c.L)
    (hPn : ∀ i, P ≤ Subgroup.normalizer (d.Lf i : Set G)) (i : Fin 3) :
    CFSG.Open.pRank p (d.Lf i) = 1 := by
  have : Fact p.Prime := ⟨(D.sig_prime p hSC.1).1⟩
  let cE := c.toCtx812EOf X D.sig (fun _ hp => hp)
  have hle : ∀ j, CFSG.Open.pRank p (d.Lf j) ≤ 1 :=
    cE.pRank_Lf_le_one hSC.1 (c.conclusion76 hSC.1) d hdM hdL hP hdS hPn
  have hsum := d.pRank_L_le_add (D.sig_prime p hSC.1).2 hle
  rw [hdL, c.pRank_L_eq_three_of_isSCPrime hSC] at hsum
  have h0 := hle 0
  have h1 := hle 1
  have h2 := hle 2
  have h0' : CFSG.Open.pRank p (d.Lf 0) = 1 := by omega
  have h1' : CFSG.Open.pRank p (d.Lf 1) = 1 := by omega
  have h2' : CFSG.Open.pRank p (d.Lf 2) = 1 := by omega
  fin_cases i
  · exact h0'
  · exact h1'
  · exact h2'

theorem normalizer_axis_le_of_isSCPrime_of_inputs
    (hSE : StronglyEmbeddedFive) (hSAlt : StronglyEmbeddedSolvableAltTen)
    (hKSM : CFSG.LocalAnalysis.RankThreeUC.S15.KSMAlt)
    (c : Ctx82E3 D) (X : C4Data G D.M) {p : ℕ} (hSC : c.IsSCPrime p)
    (d : SylowThreeData G) (hdM : d.M = D.M) (hdL : d.L = c.L) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) (hdS : d.S = P ⊓ c.L)
    (hinj : Function.Injective d.Lf) (hcomp : ∀ i, Asc83CComponent D.M (d.Lf i))
    (hPn : ∀ i, P ≤ Subgroup.normalizer (d.Lf i : Set G)) (i : Fin 3) :
    Subgroup.normalizer (d.A i : Set G) ≤ D.M := by
  have hp := (D.sig_prime p hSC.1).1
  have hp2 := (D.sig_prime p hSC.1).2
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let cE := c.toCtx812EOf X D.sig (fun _ hp => hp)
  let k := cE.toSec7Core4 hSC.1
  have hr : ∀ j, CFSG.Open.pRank p (d.Lf j) = 1 :=
    c.pRank_Lf_eq_one_of_isSCPrime X hSC d hdM hdL hP hdS hPn
  have hcal : ∀ j, d.Lf j ∈ calC d.M := by
    intro j
    rw [hdM]
    exact ⟨(hcomp j).2.1, (hcomp j).2.2.1, (hcomp j).2.2.2.2⟩
  have hdvd : ∀ j, p ∣ Nat.card (d.Lf j) := by
    intro j
    exact CFSG.GroupTheory.dvd_card_of_one_le_pRank hp (hr j).ge
  have hZ : ∀ j, ¬ p ∣ Nat.card (Subgroup.center (Bar2 (d.Lf j))) := by
    intro j
    have : Group.IsPerfect (Bar2 (d.Lf j)) := ⟨(hcomp j).2.2.2.2.1⟩
    have hq := CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp
      (CFSG.pCore 2 ↥(d.Lf j))
      (CFSG.GroupTheory.not_dvd_card_of_isPGroup
        (CFSG.pCore_isPGroup (p := 2) (G := ↥(d.Lf j))) hp hp2)
    have hqr : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 (d.Lf j))) = 1 := by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top, hq,
        CFSG.SectionRank.pRank_coe_eq_openPRank, hr j]
    exact Theorem82.not_dvd_card_center_of_pRank_eq_one hp2 hqr
  have hN := d.normalizer_axis_le_of_three_calC hSE hSAlt hKSM k hdM.symm
    c.rank.le (c.five_le_of_mem_sigma hSC.1) hcal hinj hdvd hZ i
  rwa [hdM] at hN


theorem exists_sylowThreeData_of_not_quasisimple
    (c : Ctx82E3 D) (X : C4Data G D.M)
    (h812 : ¬ CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ∃ d : SylowThreeData G, d.M = D.M ∧ d.L = c.L ∧ d.S = P ⊓ c.L ∧
      Function.Injective d.Lf ∧ (∀ i, Asc83CComponent D.M (d.Lf i)) ∧
      ∀ m ∈ D.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j := by
  exact (c.toCtx812 X).exists_sylowThreeData h812 hP

theorem le_L_of_normalizes_factors
    (hK8 : OuterThreeSplit) (c : Ctx82E3 D) (X : C4Data G D.M)
    (d : SylowThreeData G) (hdM : d.M = D.M) (hdL : d.L = c.L)
    (hcomp : ∀ i, Asc83CComponent D.M (d.Lf i))
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hdS : d.S = P ⊓ c.L) (hPn : ∀ i, P ≤ Subgroup.normalizer (d.Lf i : Set G)) :
    P ≤ c.L := by
  have hker := (c.toCtx812 X).inf_iInf_normalizer_Lf_eq hK8 d hdM hdL hcomp hP hdS
  rw [inf_eq_left.mpr (le_iInf hPn)] at hker
  exact (le_of_eq hker).trans inf_le_right

theorem mem_AA_of_cube_eq_one_of_normalizes_factors
    (hK8 : OuterThreeSplit) (c : Ctx82E3 D) (X : C4Data G D.M)
    (d : SylowThreeData G) (hdM : d.M = D.M) (hdL : d.L = c.L)
    (hcomp : ∀ i, Asc83CComponent D.M (d.Lf i))
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hdS : d.S = P ⊓ c.L) (hPn : ∀ i, P ≤ Subgroup.normalizer (d.Lf i : Set G))
    {a : G} (ha : a ∈ P) (ha3 : a ^ 3 = 1) : a ∈ d.AA := by
  have hPL := c.le_L_of_normalizes_factors hK8 X d hdM hdL hcomp hP hdS hPn
  exact d.mem_AA_of_pow_eq_one (by rw [hdS]; exact ⟨ha, hPL ha⟩) ha3

end Ctx82E3

namespace SCFixedAxes

theorem exists_prime_order_centralizing_pair (d : SylowThreeData G) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hRank : ∀ i, 1 ≤ CFSG.Open.pRank p (d.Lf i))
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) :
    ∃ y ∈ d.M ⊓ Subgroup.centralizer ((d.A j ⊔ d.A k : Subgroup G) : Set G),
      orderOf y = p := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hRL, hRel, hRcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (d.Lf i)
  have hRrank : 1 ≤ CFSG.Open.pRank p R :=
    (hRank i).trans (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hRel hRcard)
  let B := d.A j ⊔ d.A k
  let N := CFSG.Open.pCoreOf 2 d.M
  have hNM : N ≤ d.M := CFSG.LieType.BorelTits.pCoreOf_le 2 d.M
  have hNnorm : d.M ≤ Subgroup.normalizer (N : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 d.M
  have hRM : R ≤ d.M := hRL.trans (d.hLM i)
  have hAjM : d.A j ≤ d.M := (d.A_le_H j).trans ((d.H_le_Lf j).trans (d.hLM j))
  have hAkM : d.A k ≤ d.M := (d.A_le_H k).trans ((d.H_le_Lf k).trans (d.hLM k))
  have hBN : B ≤ Subgroup.normalizer (N : Set G) := (sup_le hAjM hAkM).trans hNnorm
  have hN2 : IsPGroup 2 N := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 d.M
  have hpN : ¬ p ∣ Nat.card N := CFSG.GroupTheory.not_dvd_card_of_isPGroup hN2 hp hp2
  have h3N : ¬ 3 ∣ Nat.card N :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hN2 Nat.prime_three (by norm_num)
  have hB3 : IsPGroup 3 B := d.hS.isPGroup.to_le (sup_le (d.A_le_S j) (d.A_le_S k))
  have hcommj : ⁅d.A j, R⁆ ≤ N :=
    (Subgroup.commutator_mono ((d.A_le_H j).trans (d.H_le_Lf j)) hRL).trans
      (d.hcomm j i hij.symm)
  have hcommk : ⁅d.A k, R⁆ ≤ N :=
    (Subgroup.commutator_mono ((d.A_le_H k).trans (d.H_le_Lf k)) hRL).trans
      (d.hcomm k i hik.symm)
  have hcomm : ⁅R, B⁆ ≤ N := by
    rw [Subgroup.commutator_comm]
    exact CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize
      (d.A j) (d.A k) R N hcommj hcommk (hAjM.trans hNnorm) (hAkM.trans hNnorm)
  have hcent : CFSG.Open.pRank p R ≤
      CFSG.Open.pRank p (d.M ⊓ Subgroup.centralizer (B : Set G)) :=
    CFSG.GroupTheory.pRank_le_pRank_inf_centralizer_of_commutator_le
      hRM hNM (hRM.trans hNnorm) hBN hRel.isPGroup hB3 hpN h3N hcomm
  exact CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank hp (hRrank.trans hcent)

theorem normalizer_AA_le_of_axes (d : SylowThreeData G) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p d.M)
    (hRank : ∀ i, 1 ≤ CFSG.Open.pRank p (d.Lf i))
    (hN : ∀ i, Subgroup.normalizer (d.A i : Set G) ≤ d.M) :
    Subgroup.normalizer (d.AA : Set G) ≤ d.M := by
  classical
  obtain ⟨a₀, ha₀⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top (d.A 0)).mp (d.isCyclic_A 0)
  obtain ⟨a₁, ha₁⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top (d.A 1)).mp (d.isCyclic_A 1)
  obtain ⟨a₂, ha₂⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top (d.A 2)).mp (d.isCyclic_A 2)
  have hm₀ : a₀ ∈ d.A 0 := ha₀ ▸ Subgroup.mem_zpowers a₀
  have hm₁ : a₁ ∈ d.A 1 := ha₁ ▸ Subgroup.mem_zpowers a₁
  have hm₂ : a₂ ∈ d.A 2 := ha₂ ▸ Subgroup.mem_zpowers a₂
  have ho₀ : a₀ ^ 3 = 1 := ((d.mem_A_iff 0).mp hm₀).2
  have ho₁ : a₁ ^ 3 = 1 := ((d.mem_A_iff 1).mp hm₁).2
  have ho₂ : a₂ ^ 3 = 1 := ((d.mem_A_iff 2).mp hm₂).2
  have hA : ∀ x ∈ d.AA, ∃ i j k : ℕ, x = a₀ ^ i * a₁ ^ j * a₂ ^ k := by
    intro x hx
    have hgen : d.AA = Subgroup.zpowers a₀ ⊔ Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂ := by
      rw [ha₀, ha₁, ha₂, d.AA_def]
    have hab : (Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂ : Subgroup G) ≤ d.AA := by
      rw [ha₁, ha₂, d.AA_def]
      exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
    have hz₀ : Subgroup.zpowers a₀ ≤ d.AA := by
      rw [ha₀, d.AA_def]
      exact le_sup_left.trans le_sup_left
    have hx' : x ∈ Subgroup.zpowers a₀ ⊔ (Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂) := by
      rwa [hgen, sup_assoc] at hx
    obtain ⟨u, hu, v, hv, huv⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
        (fun u hu v hv => d.S_commute u v (d.AA_le_S (hz₀ hu)) (d.AA_le_S (hab hv))) hx'
    obtain ⟨v₁, hv₁, v₂, hv₂, hv12⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
        (fun u hu v hv => d.S_commute u v (d.A_le_S 1 (ha₁ ▸ hu))
          (d.A_le_S 2 (ha₂ ▸ hv))) hv
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hu)
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hv₁)
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hv₂)
    exact ⟨i, j, k, by rw [← huv, ← hv12, ← hi, ← hj, ← hk, mul_assoc]⟩
  have hne : a₂ ∉ Subgroup.zpowers a₁ := by
    intro hm
    have hLf₁ : a₂ ∈ d.Lf 1 := (d.H_le_Lf 1) (d.A_le_H 1 (ha₁ ▸ hm))
    have hLf₂ : a₂ ∈ d.Lf 2 := (d.H_le_Lf 2) (d.A_le_H 2 hm₂)
    have ha2one := d.eq_one_of_mem_Lf_of_mem_sup (i := 2) (j := 1) (k := 0)
      (by decide) (by decide) (by decide) (d.A_le_S 2 hm₂) hLf₂
      (Subgroup.mem_sup_left hLf₁)
    have hcard : Nat.card (d.A 2) = 1 := by
      rw [← ha₂, ha2one]
      simp
    rw [d.card_A 2] at hcard
    norm_num at hcard
  have hcomm₀₁ := d.S_commute a₀ a₁ (d.A_le_S 0 hm₀) (d.A_le_S 1 hm₁)
  have hcomm₀₂ := d.S_commute a₀ a₂ (d.A_le_S 0 hm₀) (d.A_le_S 2 hm₂)
  have hcomm₁₂ := d.S_commute a₁ a₂ (d.A_le_S 1 hm₁) (d.A_le_S 2 hm₂)
  have hp12 := exists_prime_order_centralizing_pair d hp hp2 hRank (i := 0) (j := 1)
    (k := 2) (by decide) (by decide)
  have hp01 := exists_prime_order_centralizing_pair d hp hp2 hRank (i := 2) (j := 0)
    (k := 1) (by decide) (by decide)
  have hp02 := exists_prime_order_centralizing_pair d hp hp2 hRank (i := 1) (j := 0)
    (k := 2) (by decide) (by decide)
  apply UC22.R8107E3.normalizer_le_of_axes hsp ho₀ ho₁ ho₂ hcomm₀₁ hcomm₀₂ hcomm₁₂ hne
    (by rw [d.AA_def]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hm₁))
    (by rw [d.AA_def]; exact Subgroup.mem_sup_right hm₂) hA
    (by rw [ha₁]; exact hN 1) (by rw [ha₂]; exact hN 2) (fun _ => by rw [ha₀]; exact hN 0)
  · obtain ⟨y, hy, hyo⟩ := hp12
    exact ⟨y, hy.1, hyo,
      (Subgroup.mem_centralizer_iff.mp hy.2 a₁ (Subgroup.mem_sup_left hm₁)).symm,
      (Subgroup.mem_centralizer_iff.mp hy.2 a₂ (Subgroup.mem_sup_right hm₂)).symm⟩
  · intro _
    obtain ⟨y, hy, hyo⟩ := hp01
    exact ⟨y, hy.1, hyo,
      (Subgroup.mem_centralizer_iff.mp hy.2 a₀ (Subgroup.mem_sup_left hm₀)).symm,
      (Subgroup.mem_centralizer_iff.mp hy.2 a₁ (Subgroup.mem_sup_right hm₁)).symm⟩
  · intro _
    obtain ⟨y, hy, hyo⟩ := hp02
    exact ⟨y, hy.1, hyo,
      (Subgroup.mem_centralizer_iff.mp hy.2 a₀ (Subgroup.mem_sup_left hm₀)).symm,
      (Subgroup.mem_centralizer_iff.mp hy.2 a₂ (Subgroup.mem_sup_right hm₂)).symm⟩


theorem not_dvd_card_centralizer_AA_of_fixed_factors
    (c : Ctx82E3 D) {p : ℕ} (hSC : c.IsSCPrime p)
    (d : SylowThreeData G) (hdM : d.M = D.M) (hdL : d.L = c.L) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) (hdS : d.S = P ⊓ c.L)
    (hinj : Function.Injective d.Lf)
    (hperm : ∀ m ∈ D.M, ∀ i,
      ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (hPn : ∀ i, P ≤ Subgroup.normalizer (d.Lf i : Set G))
    (hrank : ∀ i, CFSG.Open.pRank p (d.Lf i) = 1) :
    ¬ p ∣ Nat.card ↥(D.M ⊓ Subgroup.centralizer (d.AA : Set G)) := by
  classical
  let cE := c.toCtx812EOfSubset D.sig (fun _ hp => hp)
  have hp : p.Prime := (D.sig_prime p hSC.1).1
  have : Fact p.Prime := ⟨hp⟩
  intro hdiv
  obtain ⟨e0, heOrder0⟩ := exists_prime_orderOf_dvd_card' p hdiv
  let e : G := e0
  have heM : e ∈ D.M ⊓ Subgroup.centralizer (d.AA : Set G) := e0.2
  have heOrder : orderOf e = p := by simpa only [e, Subgroup.orderOf_coe] using heOrder0
  have he1 : e ≠ 1 := by intro h; rw [h, orderOf_one] at heOrder; exact hp.ne_one heOrder.symm
  have heP : IsPGroup p (Subgroup.zpowers e) := by
    apply CFSG.Open.IsElemAbelian.isPGroup
    exact CFSG.Open.isElemAbelian_zpowers (by rw [← heOrder]; exact pow_orderOf_eq_one e)
  have heN : ∀ i, e ∈ Subgroup.normalizer (d.Lf i : Set G) := fun i =>
    d.le_normalizer_Lf_of_isPGroup (c.five_le_of_mem_sigma hSC.1) hinj
      (hdM.symm ▸ hperm) (hdM.symm ▸ heM.1) heP i
  exact cE.false_of_pElement_centralizer_AA hSC.1 (c.conclusion76 hSC.1) d hdM hdL
    hP hdS hPn hrank he1 heP heM.1 heM.2 heN

theorem normalizer_le_of_cube_locus
    {P A : Subgroup G} (hAP : A ≤ P) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hP3 : ∀ a ∈ P, a ^ 3 = 1 → a ∈ A)
    (hNA : Subgroup.normalizer (A : Set G) ≤ D.M) :
    Subgroup.normalizer (P : Set G) ≤ D.M := by
  intro g hg
  apply hNA
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro a ⟨x, hx, rfl⟩
    apply hP3
    · have hPmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
      rw [← hPmap]
      exact ⟨x, hAP hx, rfl⟩
    · rw [← map_pow, hA3 x hx, map_one]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem isSylowOf_top_of_cube_locus
    {P A : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hAP : A ≤ P) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hP3 : ∀ a ∈ P, a ^ 3 = 1 → a ∈ A)
    (hNA : Subgroup.normalizer (A : Set G) ≤ D.M) :
    CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ := by
  have hNP := normalizer_le_of_cube_locus hAP hA3 hP3 hNA
  apply CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le (H := D.M)
  · simpa using hP
  · simpa using hNP


theorem normalizer_and_sylow_of_fixed_factors
    (hK8 : OuterThreeSplit)
    (hSE : StronglyEmbeddedFive) (hSAlt : StronglyEmbeddedSolvableAltTen)
    (hKSM : CFSG.LocalAnalysis.RankThreeUC.S15.KSMAlt)
    (c : Ctx82E3 D) (X : Ctx82E3.C4Data G D.M) {p : ℕ} (hSC : c.IsSCPrime p)
    (d : SylowThreeData G) (hdM : d.M = D.M) (hdL : d.L = c.L)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hdS : d.S = P ⊓ c.L) (hinj : Function.Injective d.Lf)
    (hcomp : ∀ i, Asc83CComponent D.M (d.Lf i))
    (hPn : ∀ i, P ≤ Subgroup.normalizer (d.Lf i : Set G)) :
    Subgroup.normalizer (P : Set G) ≤ D.M ∧ CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ := by
  have hRank := c.pRank_Lf_eq_one_of_isSCPrime X hSC d hdM hdL hP hdS hPn
  have hN := c.normalizer_axis_le_of_isSCPrime_of_inputs hSE hSAlt hKSM X hSC
    d hdM hdL hP hdS hinj hcomp hPn
  have hNA : Subgroup.normalizer (d.AA : Set G) ≤ D.M := by
    have hh := normalizer_AA_le_of_axes d (D.sig_prime p hSC.1).1 (D.sig_prime p hSC.1).2
      (hdM.symm ▸ c.isStronglyPEmbedded_of_mem_sigma hSC.1)
      (fun i => by rw [hRank i]) (fun i => hdM.symm ▸ hN i)
    rwa [hdM] at hh
  have hAP : d.AA ≤ P := d.AA_le_S.trans (by rw [hdS]; exact inf_le_left)
  have hAc : ∀ a ∈ d.AA, a ^ 3 = 1 := fun a ha => d.isElemAbelian_AA.2 a ha
  have hPc : ∀ a ∈ P, a ^ 3 = 1 → a ∈ d.AA := fun a ha h3 =>
    c.mem_AA_of_cube_eq_one_of_normalizes_factors hK8 X d hdM hdL hcomp hP hdS hPn ha h3
  exact ⟨normalizer_le_of_cube_locus hAP hAc hPc hNA,
    isSylowOf_top_of_cube_locus hP hAP hAc hPc hNA⟩


theorem exists_centralizer_not_le_of_fixed_factors
    (hK8 : OuterThreeSplit)
    (hSE : StronglyEmbeddedFive) (hSAlt : StronglyEmbeddedSolvableAltTen)
    (hKSM : CFSG.LocalAnalysis.RankThreeUC.S15.KSMAlt)
    (c : Ctx82E3 D) (X : Ctx82E3.C4Data G D.M) {p : ℕ} (hSC : c.IsSCPrime p)
    (d : SylowThreeData G) (hdM : d.M = D.M) (hdL : d.L = c.L)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hdS : d.S = P ⊓ c.L) (hinj : Function.Injective d.Lf)
    (hcomp : ∀ i, Asc83CComponent D.M (d.Lf i))
    (hPn : ∀ i, P ≤ Subgroup.normalizer (d.Lf i : Set G)) :
    ∃ a ∈ d.AA, a ≠ 1 ∧ ¬ Subgroup.centralizer ({a} : Set G) ≤ D.M := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hNP, hPG⟩ := normalizer_and_sylow_of_fixed_factors hK8 hSE hSAlt hKSM
    c X hSC d hdM hdL hP hdS hinj hcomp hPn
  by_contra hnone
  push Not at hnone
  have hPne : P ≠ ⊥ := by
    intro hbot
    have hAA : d.AA ≤ P := d.AA_le_S.trans (by rw [hdS]; exact inf_le_left)
    have hAbot : d.AA = ⊥ := le_bot_iff.mp (hbot ▸ hAA)
    have hc := d.card_AA
    rw [hAbot, Subgroup.card_bot] at hc
    norm_num at hc
  apply c.not_strong
  apply CFSG.RankThree.PartOne.isStronglyPEmbedded_of_normalizer_sylow_le c.M_ne_top hP hPne hNP
  intro a ha ha3
  have haAA := c.mem_AA_of_cube_eq_one_of_normalizes_factors hK8 X d hdM hdL hcomp hP hdS hPn
    ha (by rw [← ha3]; exact pow_orderOf_eq_one a)
  exact hnone a haAA (by intro h1; rw [h1, orderOf_one] at ha3; omega)

end SCFixedAxes

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
