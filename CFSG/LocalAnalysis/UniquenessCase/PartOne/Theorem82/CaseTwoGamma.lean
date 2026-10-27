module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
public import CFSG.Open.RankThreeDefs
import CFSG.RankThree.PartOne.S12.Sec159Tools
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LieType.BorelTits.Basic
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.RankThree.PartOne.S11d.OutCentral
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorSupLeOfCommutatorLeAndNormalize

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SylowThreeData

open Subgroup
open scoped Pointwise commutatorElement

theorem sup_pCore_le_rankThreeGamma
    {G : Type} [Group G] [Finite G] (d : SylowThreeData G) :
    d.L ⊔ CFSG.Open.pCoreOf 2 d.M ≤ CFSG.Open.rankThreeGamma 2 3 d.AA := by
  classical
  let R : Subgroup G := CFSG.Open.pCoreOf 2 d.M
  let Γ : Subgroup G := CFSG.Open.rankThreeGamma 2 3 d.AA
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 d.M
  have hMR : d.M ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) d.M
  have hR3 : ¬ 3 ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := hR2.exists_card_eq
    rw [hn]
    intro hdiv
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdiv
    norm_num at h32
  have hAMle : ∀ l : Fin 3, d.A l ≤ d.M := fun l =>
    ((d.A_le_H l).trans (d.H_le_Lf l)).trans (d.hLM l)
  have hAM : d.AA ≤ d.M := by
    rw [d.AA_def]
    exact sup_le (sup_le (hAMle 0) (hAMle 1)) (hAMle 2)
  have hAMR : d.AA ≤ Subgroup.normalizer (R : Set G) := hAM.trans hMR
  have hN : ∀ B : Subgroup G, B ≤ d.AA → ¬ IsCyclic ↥B →
      Subgroup.normalizer (B : Set G) ≤ Γ := by
    intro B hBA hBnc
    have hBel : CFSG.Open.IsElemAbelian 3 B := d.isElemAbelian_AA.mono hBA
    have hB3 : IsPGroup 3 B := hBel.isPGroup
    have hrankGroup : 2 ≤ CFSG.pRank 3 ↥B := by
      by_contra h
      have hle : CFSG.pRank 3 ↥B ≤ 1 := by omega
      exact hBnc (CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one
        (p := 3) Nat.prime_three (by norm_num) le_rfl hB3 hle)
    have hrank : 2 ≤ CFSG.Open.pRank 3 B := by
      rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at hrankGroup
    have hΓ : Γ = CFSG.Open.GLBCore 3 2 d.AA := rfl
    rw [hΓ]
    unfold CFSG.Open.GLBCore
    exact le_sSup ⟨B, hBA, hrank, rfl⟩
  have hRΓ : R ≤ Γ :=
    CFSG.RankThree.PartOne.Sec159.le_of_pPrime_normalized
      (p := 3) Nat.prime_three (A := d.AA) (Z := R) (N := Γ)
      d.isElemAbelian_AA.isElementaryAbelian (by rw [d.card_AA]; norm_num)
      hN hAMR hR3
  have hfactor : ∀ (i j k : Fin 3), i ≠ j → i ≠ k → j ≠ k → d.Lf i ≤ Γ := by
    intro i j k hij hik hjk
    let B : Subgroup G := d.A j ⊔ d.A k
    have hAleAA : ∀ l : Fin 3, d.A l ≤ d.AA := by
      intro l
      rw [d.AA_def]
      fin_cases l
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    have hBAA : B ≤ d.AA := sup_le (hAleAA j) (hAleAA k)
    have hBM : B ≤ d.M := sup_le (hAMle j) (hAMle k)
    have hB3 : IsPGroup 3 B := (d.isElemAbelian_AA.mono hBAA).isPGroup
    have hBnc : ¬ IsCyclic ↥B := by
      intro hcyc
      have hcardj : Nat.card ↥((d.A j).subgroupOf B) = 3 := by
        rw [Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (le_sup_left : d.A j ≤ B)).toEquiv]
        exact d.card_A j
      have hcardk : Nat.card ↥((d.A k).subgroupOf B) = 3 := by
        rw [Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (le_sup_right : d.A k ≤ B)).toEquiv]
        exact d.card_A k
      have heq : (d.A j).subgroupOf B = (d.A k).subgroupOf B :=
        (@IsCyclic.subgroup_eq_iff_card_eq ↥B _ hcyc _ _ _ _).mpr
          (hcardj.trans hcardk.symm)
      have hone : ∀ x ∈ d.A j, x = 1 := by
        intro x hx
        have hxB : x ∈ B := (le_sup_left : d.A j ≤ B) hx
        have hmemj : (⟨x, hxB⟩ : ↥B) ∈ (d.A j).subgroupOf B := by
          rwa [Subgroup.mem_subgroupOf]
        have hmemb : (⟨x, hxB⟩ : ↥B) ∈ (d.A k).subgroupOf B := by
          rwa [heq] at hmemj
        have hxAk : x ∈ d.A k := by
          simpa using (Subgroup.mem_subgroupOf.mp hmemb)
        exact d.eq_one_of_mem_Lf_of_mem_sup (i := j) (j := k) (k := i) hjk hij.symm
          hik.symm ((d.A_le_S j) hx) ((d.H_le_Lf j) ((d.A_le_H j) hx))
          (Subgroup.mem_sup_left ((d.H_le_Lf k) ((d.A_le_H k) hxAk)))
      have hnt : Nontrivial ↥(d.A j) := by
        rw [← Finite.one_lt_card_iff_nontrivial, d.card_A j]
        norm_num
      obtain ⟨a, ha1⟩ := exists_ne (1 : ↥(d.A j))
      exact ha1 (Subtype.ext (hone (a : G) a.2))
    have hBΓ : Subgroup.normalizer (B : Set G) ≤ Γ := hN B hBAA hBnc
    have hcommj : ⁅d.A j, d.Lf i⁆ ≤ R :=
      (Subgroup.commutator_mono ((d.A_le_H j).trans (d.H_le_Lf j)) le_rfl).trans
        (d.hcomm j i hij.symm)
    have hcommk : ⁅d.A k, d.Lf i⁆ ≤ R :=
      (Subgroup.commutator_mono ((d.A_le_H k).trans (d.H_le_Lf k)) le_rfl).trans
        (d.hcomm k i hik.symm)
    have hBRcomm : ⁅B, d.Lf i⁆ ≤ R :=
      CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize
        (d.A j) (d.A k) (d.Lf i) R hcommj hcommk
        ((hAMle j).trans hMR) ((hAMle k).trans hMR)
    intro x hx
    have hxM : x ∈ d.M := d.hLM i hx
    have hxN : x ∈ Subgroup.normalizer (R : Set G) := hMR hxM
    have hxcomm : ∀ u ∈ B, u * x * u⁻¹ * x⁻¹ ∈ R := by
      intro u hu
      have hmem : ⁅u, x⁆ ∈ ⁅B, d.Lf i⁆ :=
        Subgroup.commutator_mem_commutator hu hx
      have := hBRcomm hmem
      rwa [commutatorElement_def] at this
    obtain ⟨v, hvR, hfix⟩ := CFSG.RankThree.PartOne.Sec159.exists_fixed_in_coset
      (p := 3) (U := B) (V := R) hB3 hR3 (hBM.trans hMR) hxN hxcomm
    have hxvCent : x * v ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact mul_inv_eq_iff_eq_mul.mp (hfix u hu)
    have hxvΓ : x * v ∈ Γ :=
      hBΓ (Subgroup.centralizer_le_normalizer (B : Set G) hxvCent)
    have hxΓ : x ∈ Γ := by
      have h1 : (x * v) * v⁻¹ ∈ Γ := Γ.mul_mem hxvΓ (Γ.inv_mem (hRΓ hvR))
      simpa using h1
    exact hxΓ
  have hLΓ : d.L ≤ Γ := by
    rw [d.hL]
    exact sup_le (sup_le (hfactor 0 1 2 (by decide) (by decide) (by decide))
      (hfactor 1 0 2 (by decide) (by decide) (by decide)))
      (hfactor 2 0 1 (by decide) (by decide) (by decide))
  exact sup_le hLΓ hRΓ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SylowThreeData

end
