module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_1_b
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Theorem 10.1(d) from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
omit [IsMinCE G] in
/- Theorem 10.1(d). -/
public theorem CFSG.theorem_10_1_d
    {M : Subgroup G} {p : Nat.Primes}
    (_hM : M ∈ section9MaximalSubgroups G) (hpσ : p ∈ section10SigmaPrimes M)
    (X : Sylow p.val M) {g : G}
    (hXgM : (section10AmbientSylowSubgroup M X).conjBy g ≤ M) :
    g ∈ M := by
  exact section10_sylow_conjugate_mem_of_normalizer_le X
    (section10_sigma_sylow_normalizer_le hpσ X) hXgM

end Section10
