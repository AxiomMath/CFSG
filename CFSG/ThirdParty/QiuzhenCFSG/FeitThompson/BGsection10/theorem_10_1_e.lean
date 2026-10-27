module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_1_a
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Theorem 10.1(e) from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
/-- Theorem 10.1(e). -/
public theorem CFSG.theorem_10_1_e
    {M X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpσ : p ∈ section10SigmaPrimes M)
    (hXne : X ≠ ⊥) (hXp : IsPGroup p.val X) (hXM : X ≤ M)
    (hCXM : Subgroup.centralizer (X : Set G) ≤ M) {g : G}
    (hXgM : X.conjBy g ≤ M) :
    g ∈ M := by
  rcases theorem_10_1_a hM hpσ hXne hXp hXM hXgM with ⟨m, c, hg⟩
  rw [hg]
  exact M.mul_mem m.property (hCXM c.property)

end Section10
