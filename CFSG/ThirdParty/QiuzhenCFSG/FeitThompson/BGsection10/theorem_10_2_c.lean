module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_2_b

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Theorem 10.2(c) from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Theorem 10.2(c). -/
public theorem CFSG.theorem_10_2_c
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    section10MalphaSubgroup M ≤ section10MsigmaSubgroup M ∧
      section10MsigmaSubgroup M ≤ derivedSubgroup M := by
  exact ⟨section10_malphaSubgroup_le_msigmaSubgroup hM,
    section10_msigmaSubgroup_le_derivedSubgroup hM⟩

end Section10
