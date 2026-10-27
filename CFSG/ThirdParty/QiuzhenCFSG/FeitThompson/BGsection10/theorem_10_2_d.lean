module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_2_c
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Theorem 10.2(d) from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

private theorem CFSG.section10_quotient_malpha_groupRank_le_two
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    groupRank (M ⧸ section10MalphaSubgroup M) ≤ 2 := by
  classical
  let π : Set Nat.Primes := section10AlphaPrimes M
  let K : Subgroup M := section10MalphaSubgroup M
  let Q := M ⧸ K
  have hKHall : IsHallSubgroup π K := section10_malphaSubgroup_isHall hM
  rw [groupRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, 2, Nat.prime_two, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨q, hqprime, hnq⟩
    by_cases hn_le_two : n ≤ 2
    · exact hn_le_two
    have hthree_n : 3 ≤ n := by omega
    let p : Nat.Primes := ⟨q, hqprime⟩
    haveI : Fact p.val.Prime := ⟨p.property⟩
    have hthree_rank_Q : 3 ≤ primeRank p.val Q := hthree_n.trans hnq
    have hp_dvd_Q : p.val ∣ Nat.card Q :=
      section10_prime_dvd_card_of_three_le_primeRank_pre
        (p := p.val) (R := Q) hthree_rank_Q
    have hp_not_alpha : p ∉ π := by
      intro hpα
      exact (hKHall.p_in_pi_of_p_dvd_index p (by
        simpa [Q, K, Subgroup.index_eq_card] using hp_dvd_Q)) hpα
    have hprankQ_le_M : primeRank p.val Q ≤ primeRank p.val M := by
      change primeRank p.val (M ⧸ piCore (section10AlphaPrimes M) M) ≤
        primeRank p.val M
      exact section10_primeRank_quotient_piCore_le_of_not_mem
        (H := M) (π := section10AlphaPrimes M) (p := p) (by
          simpa [π] using hp_not_alpha)
    have hp_dvd_M : p.val ∣ Nat.card M :=
      hp_dvd_Q.trans (Subgroup.card_quotient_dvd_card (s := K))
    have hprankM_le_two : primeRank p.val M ≤ 2 := by
      by_contra hnot
      have hgt : 2 < primeRank p.val M := Nat.lt_of_not_ge hnot
      exact hp_not_alpha (by
        simpa [π, section10AlphaPrimes, subgroupPrimeSet] using
          (show p ∈ section10AlphaPrimes M from ⟨hp_dvd_M, hgt⟩))
    exact hnq.trans (hprankQ_le_M.trans hprankM_le_two)

/-- Theorem 10.2(d). -/
public theorem CFSG.theorem_10_2_d
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    groupRank (M ⧸ section10MalphaSubgroup M) ≤ 2 ∧
      section10QuotientNilpotent (derivedSubgroup M) (section10MalphaSubgroup M) := by
  exact ⟨section10_quotient_malpha_groupRank_le_two hM,
    section10_derivedSubgroup_quotient_malpha_nilpotent hM⟩

end Section10
