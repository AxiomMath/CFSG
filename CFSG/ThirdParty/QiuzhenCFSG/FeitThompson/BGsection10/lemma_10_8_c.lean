module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_8_b
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

/-- Lemma 10.8(c). -/
public theorem CFSG.lemma_10_8_c
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hpM : p ∈ subgroupPrimeSet M) (hpβ : p ∉ section10BetaPrimes M) :
    HasNormalPComplement p.val (derivedSubgroup M) ∧
      HasNormalPComplement p.val (section10MsigmaSubgroup M) ∧
      IsLargestPrimeDivisor p.val (Nat.card (M ⧸ pPrimeCore p.val M)) := by
  exact section10_normalPComplements_of_not_mem_beta hM hpM hpβ

