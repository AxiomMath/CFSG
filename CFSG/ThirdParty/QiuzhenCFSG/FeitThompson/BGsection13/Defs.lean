module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_19
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Data.Finset.NatDivisors
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Definitions from BG Section 13

This file records a statement-only scaffold for Section 13 of
`Local Analysis for the Odd Order Theorem`.
-/

section Notation

variable {G : Type*} [Group G] [Finite G]

/-- `A` acts in a prime manner on `H`: `A` normalizes `H`, and for every
prime-order subgroup `P ≤ A`, `C_H(P) ≤ C_H(A)`. -/
@[expose] public def CFSG.section13ActsPrimeManner
    (A H : Subgroup G) : Prop :=
  A ≤ Subgroup.normalizer (H : Set G) ∧
    ∀ P : Subgroup G, P ∈ section12PrimeOrderSubgroups A →
      subgroupCentralizerIn H P ≤ subgroupCentralizerIn H A

/-- `A` acts regularly on `H`: `A` normalizes `H`, and every nonidentity
element of `A` has trivial centralizer in `H`. -/
@[expose] public def CFSG.section13ActsRegularlyOn
    (A H : Subgroup G) : Prop :=
  A ≤ Subgroup.normalizer (H : Set G) ∧
    ∀ a : G, a ∈ A → a ≠ 1 → elementCentralizerIn H a = ⊥

end Notation
