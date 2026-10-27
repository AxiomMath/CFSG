module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_2_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_20_a
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Theorem 10.2(b) from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

public theorem CFSG.section10_fitting_quotient_msigma_groupRank_le_two
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    groupRank (fittingSubgroup (M ⧸ section10MsigmaSubgroup M)) ≤ 2 := by
  classical
  let π : Set Nat.Primes := section10SigmaPrimes M
  let Q := M ⧸ section10MsigmaSubgroup M
  let F : Subgroup Q := fittingSubgroup Q
  have hFπc : IsPiSubgroup (G := Q) πᶜ F := by
    change IsPiSubgroup
      (G := M ⧸ piCore (section10SigmaPrimes M) M)
      (section10SigmaPrimes M)ᶜ
      (fittingSubgroup (M ⧸ piCore (section10SigmaPrimes M) M))
    exact section10_fitting_quotient_piCore_isPiSubgroup_compl
      (H := M) (π := section10SigmaPrimes M)
  rw [groupRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, 2, Nat.prime_two, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨q, hqprime, hnq⟩
    by_cases hn_le_two : n ≤ 2
    · exact hn_le_two
    have hthree_n : 3 ≤ n := by omega
    let p : Nat.Primes := ⟨q, hqprime⟩
    have : Fact p.val.Prime := ⟨p.property⟩
    have hthree_rank_F : 3 ≤ primeRank p.val F := hthree_n.trans hnq
    have hp_dvd_F : p.val ∣ Nat.card F :=
      section10_prime_dvd_card_of_three_le_primeRank_pre
        (p := p.val) (R := F) hthree_rank_F
    have hp_not_sigma : p ∉ π := by
      have hp_compl : p ∈ πᶜ := hFπc p hp_dvd_F
      simpa using hp_compl
    have hprankF_le_Q : primeRank p.val F ≤ primeRank p.val Q := by
      simpa [Q, F, p] using section8_primeRank_le_of_subgroup (G := Q) F p.val
    have hprankQ_le_M : primeRank p.val Q ≤ primeRank p.val M := by
      change primeRank p.val (M ⧸ piCore (section10SigmaPrimes M) M) ≤
        primeRank p.val M
      exact section10_primeRank_quotient_piCore_le_of_not_mem
        (H := M) (π := section10SigmaPrimes M) (p := p) (by
          simpa [π] using hp_not_sigma)
    have hp_dvd_M : p.val ∣ Nat.card M := by
      exact (hp_dvd_F.trans (Subgroup.card_subgroup_dvd_card F)).trans
        (Subgroup.card_quotient_dvd_card (s := section10MsigmaSubgroup M))
    have hprankM_le_two : primeRank p.val M ≤ 2 := by
      by_contra hnot
      have hgt : 2 < primeRank p.val M := Nat.lt_of_not_ge hnot
      have hp_alpha : p ∈ section10AlphaPrimes M := by
        simpa [section10AlphaPrimes, subgroupPrimeSet] using
          (show p ∈ section10AlphaPrimes M from ⟨hp_dvd_M, hgt⟩)
      exact hp_not_sigma (section10_alpha_subset_sigma hM hp_alpha)
    exact hnq.trans (hprankF_le_Q.trans (hprankQ_le_M.trans hprankM_le_two))

public theorem CFSG.section10_prime_not_dvd_derived_quotient_msigma_of_mem_sigma
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hpσ : p ∈ section10SigmaPrimes M) :
    ¬ p.val ∣ Nat.card (derivedSubgroup M ⧸
      (section10MsigmaSubgroup M).subgroupOf (derivedSubgroup M)) := by
  classical
  intro hp_dvd
  let π : Set Nat.Primes := section10SigmaPrimes M
  let K : Subgroup M := section10MsigmaSubgroup M
  let Q := M ⧸ K
  have hMsolv : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hQsolv : Group.IsSolvable Q := by
    let : Group.IsSolvable M := hMsolv
    dsimp [Q]
    infer_instance
  have hModd : Odd (Nat.card M) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
  have hQodd : Odd (Nat.card Q) :=
    hModd.of_dvd_nat (Subgroup.card_quotient_dvd_card (s := K))
  have hF_rank : groupRank (fittingSubgroup Q) ≤ 2 := by
    simpa [Q, K] using section10_fitting_quotient_msigma_groupRank_le_two hM
  have hDerQ_nil : Group.IsNilpotent (derivedSubgroup Q) :=
    theorem_4_20_a (G := Q) hQsolv hQodd (Or.inr hF_rank)
  have hDerQ_le_F : derivedSubgroup Q ≤ fittingSubgroup Q :=
    le_sSup ⟨inferInstance, hDerQ_nil⟩
  have hcard_eq :
      Nat.card (derivedSubgroup M ⧸ K.subgroupOf (derivedSubgroup M)) =
        Nat.card (derivedSubgroup Q) := by
    simpa [Q, K] using section10_card_derivedSubgroup_quotient_eq (H := M) K
  have hp_dvd_derQ : p.val ∣ Nat.card (derivedSubgroup Q) := by
    rw [← hcard_eq]
    simpa [K] using hp_dvd
  have hp_dvd_F : p.val ∣ Nat.card (fittingSubgroup Q) :=
    hp_dvd_derQ.trans (Subgroup.card_dvd_of_le hDerQ_le_F)
  have hFπc :
      IsPiSubgroup (G := Q) πᶜ (fittingSubgroup Q) := by
    change IsPiSubgroup
      (G := M ⧸ piCore (section10SigmaPrimes M) M)
      (section10SigmaPrimes M)ᶜ
      (fittingSubgroup (M ⧸ piCore (section10SigmaPrimes M) M))
    exact section10_fitting_quotient_piCore_isPiSubgroup_compl
      (H := M) (π := section10SigmaPrimes M)
  exact (hFπc p hp_dvd_F) hpσ

public theorem CFSG.section10_msigmaSubgroup_isHall
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) := by
  classical
  let π : Set Nat.Primes := section10SigmaPrimes M
  let K : Subgroup M := section10MsigmaSubgroup M
  refine isHallSubgroup_of (G := M) (π := π) (H := K) ?_ ?_
  · intro p hp_dvd
    simpa [K, π, section10MsigmaSubgroup] using
      (piCore_isPiSubgroup (G := M) π p hp_dvd)
  · intro p hpσ hp_dvd_index
    let D : Subgroup M := derivedSubgroup M
    have hKD : K ≤ D := section10_msigmaSubgroup_le_derivedSubgroup hM
    have hidx_mul : K.relIndex D * D.index = K.index :=
      Subgroup.relIndex_mul_index hKD
    have hp_dvd_prod : p.val ∣ K.relIndex D * D.index := by
      simpa [hidx_mul] using hp_dvd_index
    rcases p.property.dvd_or_dvd hp_dvd_prod with hp_rel | hp_Didx
    · have hrel_eq : K.relIndex D = (K.subgroupOf D).index := by
        calc
          K.relIndex D =
              (K.subgroupOf D).relIndex (D.subgroupOf D) :=
            (Subgroup.relIndex_subgroupOf
              (H := K) (K := D) (L := D) (hKL := le_rfl)).symm
          _ = (K.subgroupOf D).relIndex ⊤ := by rw [Subgroup.subgroupOf_self]
          _ = (K.subgroupOf D).index :=
            Subgroup.relIndex_top_right (H := K.subgroupOf D)
      exact section10_prime_not_dvd_derived_quotient_msigma_of_mem_sigma hM
        (by simpa [π] using hpσ) (by
          change p.val ∣ Nat.card (D ⧸ K.subgroupOf D)
          rw [← (K.subgroupOf D).index_eq_card, ← hrel_eq]
          exact hp_rel)
    · exact (section10_sigma_not_dvd_quotient_derived hM
        (by simpa [π] using hpσ)) (by
          simpa [D, Subgroup.index_eq_card] using hp_Didx)

omit [IsMinCE G] in
public theorem CFSG.section10_prime_not_dvd_maximal_index_of_mem_sigma
    {M : Subgroup G} (_hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hpσ : p ∈ section10SigmaPrimes M) :
    ¬ p.val ∣ M.index := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  intro hp_dvd_index
  let P : Sylow p.val M := Classical.choice (Sylow.nonempty (p := p.val) (G := M))
  let PG : Subgroup G := section10AmbientSylowSubgroup M P
  have hPGp : IsPGroup p.val PG := by
    change IsPGroup p.val ((P : Subgroup M).map M.subtype)
    simpa using
      (IsPGroup.map (p := p.val) (H := (P : Subgroup M)) P.isPGroup' M.subtype)
  obtain ⟨S, hPGS⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hPGp
  have hS_eq_PG : (S : Subgroup G) = PG := by
    simpa [PG] using section10_sigma_ambient_sylow_eq_of_le_sylow hpσ P S hPGS
  have hPG_not_dvd_index : ¬ p.val ∣ PG.index := by
    simpa [hS_eq_PG] using S.not_dvd_index
  have hPG_index : PG.index = (P : Subgroup M).index * M.index := by
    simpa [PG, section10AmbientSylowSubgroup] using
      (Subgroup.index_map_subtype (H := M) (K := (P : Subgroup M)))
  exact hPG_not_dvd_index (by
    rw [hPG_index]
    exact dvd_mul_of_dvd_right hp_dvd_index (P : Subgroup M).index)

public theorem CFSG.section10_msigma_isHall
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    IsHallSubgroup (section10SigmaPrimes M) (section10Msigma M) := by
  classical
  let π : Set Nat.Primes := section10SigmaPrimes M
  let K : Subgroup M := section10MsigmaSubgroup M
  have hKHall : IsHallSubgroup π K := section10_msigmaSubgroup_isHall hM
  refine isHallSubgroup_of (G := G) (π := π) (H := section10Msigma M) ?_ ?_
  · intro p hp_dvd
    have hcard_eq : Nat.card (section10Msigma M) = Nat.card K := by
      simpa [section10Msigma, K] using
        (Subgroup.card_map_of_injective (K := K) (f := M.subtype) M.subtype_injective)
    exact hKHall.p_in_pi_of_p_dvd_card p (by simpa [hcard_eq] using hp_dvd)
  · intro p hpσ hp_dvd_index
    have hidx : (section10Msigma M).index = K.index * M.index := by
      simpa [section10Msigma, K] using
        (Subgroup.index_map_subtype (H := M) (K := K))
    have hp_dvd_prod : p.val ∣ K.index * M.index := by
      simpa [hidx] using hp_dvd_index
    rcases p.property.dvd_or_dvd hp_dvd_prod with hpK | hpM
    · exact (hKHall.p_in_pi_of_p_dvd_index p hpK) hpσ
    · exact section10_prime_not_dvd_maximal_index_of_mem_sigma hM
        (by simpa [π] using hpσ) hpM

/-- Theorem 10.2(b). -/
public theorem CFSG.theorem_10_2_b
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    IsHallSubgroup (section10SigmaPrimes M) (section10Msigma M) ∧
      IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) := by
  exact ⟨section10_msigma_isHall hM, section10_msigmaSubgroup_isHall hM⟩

end Section10
