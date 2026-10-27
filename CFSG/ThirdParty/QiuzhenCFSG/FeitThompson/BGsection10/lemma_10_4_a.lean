module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_3

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Lemma 10.4(a) from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Lemma 10.4(a). -/
public theorem CFSG.lemma_10_4_a
    {M : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpdvd : p.val ∣ Nat.card (M ⧸ derivedSubgroup M)) :
    p ∉ section10AlphaPrimes M := by
  intro hpα
  exact section10_sigma_not_dvd_quotient_derived hM
    (section10_alpha_subset_sigma hM hpα) hpdvd

end Section10
