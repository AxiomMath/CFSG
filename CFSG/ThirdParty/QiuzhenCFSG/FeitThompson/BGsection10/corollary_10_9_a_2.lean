module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.corollary_10_9_a_1
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Statements from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

private theorem CFSG.section10_msigma_sylow_groupRank_ge_three_of_mem_alpha
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hpα : p ∈ section10AlphaPrimes M)
    (P : Sylow p.val (section10Msigma M)) :
    3 ≤ groupRank (P : Subgroup (section10Msigma M)) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hpσ : p ∈ section10SigmaPrimes M := section10_alpha_subset_sigma hM hpα
  have hprankM : 3 ≤ primeRank p.val M := Nat.succ_le_of_lt hpα.2
  obtain ⟨A, hAp, hAcomm, hAgen⟩ :=
    section10_exists_pSubgroup_three_le_generatorRank_of_three_le_primeRank_pre
      (p := p.val) (R := M) hprankM
  have hA_le_K : A ≤ section10MsigmaSubgroup M := by
    letI : (section10MsigmaSubgroup M).Normal := inferInstance
    exact section10_pSubgroup_le_normal_hall_of_mem_early
      (R := M) (π := section10SigmaPrimes M) (H := section10MsigmaSubgroup M)
      (P := A) hAp (section10_msigmaSubgroup_isHall hM) hpσ
  let AG : Subgroup G := A.map M.subtype
  have hAG_le_msigma : AG ≤ section10Msigma M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, haA, rfl⟩
    exact Subgroup.mem_map.mpr ⟨a, hA_le_K haA, rfl⟩
  let Aσ : Subgroup (section10Msigma M) := AG.subgroupOf (section10Msigma M)
  have hAGp : IsPGroup p.val AG := by
    simpa [AG] using IsPGroup.map (p := p.val) (H := A) hAp M.subtype
  have hAσp : IsPGroup p.val Aσ := by
    exact hAGp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := AG) (K := section10Msigma M) hAG_le_msigma).symm
  have hAGcomm : IsMulCommutative AG := by
    letI : IsMulCommutative A := hAcomm
    simpa [AG] using Subgroup.map_isMulCommutative (f := M.subtype) (H := A)
  have hAσcomm : IsMulCommutative Aσ := by
    letI : IsMulCommutative AG := hAGcomm
    exact Subgroup.subgroupOf_isMulCommutative (H := AG) (K := section10Msigma M)
  have hAG_gen_eq : generatorRank AG = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr
      (Subgroup.equivMapOfInjective (f := M.subtype) A M.subtype_injective).symm
  have hAσ_gen_eq : generatorRank Aσ = generatorRank AG := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr
      (Subgroup.subgroupOfEquivOfLe (H := AG) (K := section10Msigma M) hAG_le_msigma)
  have hAσgen : 3 ≤ generatorRank Aσ := by
    simpa [hAσ_gen_eq, hAG_gen_eq] using hAgen
  have hprimeRank_msigma : 3 ≤ primeRank p.val (section10Msigma M) := by
    rw [primeRank]
    refine le_csSup ?_ ?_
    · refine ⟨Nat.card (section10Msigma M), ?_⟩
      intro n hn
      rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
      exact hnB.trans <|
        (section10_generatorRank_le_natCard_pre B).trans (Subgroup.card_le_card_group B)
    · exact ⟨Aσ, hAσp, hAσcomm, hAσgen⟩
  exact hprimeRank_msigma.trans
    (section10_primeRank_le_groupRank_sylow_pre (G := section10Msigma M) P)

/-- Corollary 10.9(a)(2). -/
public theorem CFSG.corollary_10_9_a_2
    {M X : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpM : p ∈ subgroupPrimeSet M)
    (hqM : q ∈ subgroupPrimeSet M) (hpβ : p ∉ section10BetaPrimes M)
    (hqβ : q ∉ section10BetaPrimes M) (hpq : p ≠ q) (hXle : X ≤ M)
    (hXq : IsPGroup q.val X) (hXhyp : X ≤ ambientDerivedSubgroup M ∨ p.val < q.val)
    (hpα : p ∈ section10AlphaPrimes M) :
    subgroupCentralizerIn M X ∈ section9UniqueSubgroups G := by
  classical
  have hpσ : p ∈ section10SigmaPrimes M := section10_alpha_subset_sigma hM hpα
  obtain ⟨Pσ, hPσcent⟩ :=
    corollary_10_9_a_1
      (G := G) (M := M) (X := X) (p := p) (q := q)
      hM hpM hqM hpβ hqβ hpq hXle hXq hXhyp
  let PG : Subgroup G := section10AmbientSylowSubgroup (section10Msigma M) Pσ
  have hPG_le_CM : PG ≤ subgroupCentralizerIn M X := by
    intro y hy
    constructor
    · rcases Subgroup.mem_map.mp hy with ⟨z, _hzP, rfl⟩
      rcases z.property with ⟨m, _hm, hmz⟩
      change (z : G) ∈ M
      rw [← hmz]
      exact m.property
    · exact hPσcent hy
  have hPσ_rank : 3 ≤ groupRank (Pσ : Subgroup (section10Msigma M)) :=
    section10_msigma_sylow_groupRank_ge_three_of_mem_alpha hM hpα Pσ
  have hPG_rank : 3 ≤ groupRank PG := by
    let ePG : (Pσ : Subgroup (section10Msigma M)) ≃* PG :=
      Subgroup.equivMapOfInjective
        (Pσ : Subgroup (section10Msigma M)) (section10Msigma M).subtype
        (section10Msigma M).subtype_injective
    exact hPσ_rank.trans
      (section10_groupRank_le_of_equiv_pre
        (R := PG) (S := (Pσ : Subgroup (section10Msigma M))) ePG.symm)
  have hCM_large : 3 ≤ groupRank (subgroupCentralizerIn M X) :=
    hPG_rank.trans (section10_groupRank_le_of_le hPG_le_CM)
  exact theorem_9_6
    (K := subgroupCentralizerIn M X)
    (section10_subgroupCentralizerIn_maximal_proper hM)
    (by omega) (Or.inl hCM_large)
