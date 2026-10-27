module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_1_a
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Theorem 10.1(c) from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
/-- Theorem 10.1(c). -/
public theorem CFSG.theorem_10_1_c
    {M X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpσ : p ∈ section10SigmaPrimes M)
    (hXne : X ≠ ⊥) (hXp : IsPGroup p.val X) (hXM : X ≤ M) :
    Subgroup.normalizer (X : Set G) =
      subgroupNormalizerIn M (X : Set G) ⊔ Subgroup.centralizer (X : Set G) := by
  apply le_antisymm
  · intro g hgN
    have hXgM : X.conjBy g ≤ M := by
      rw [section10_conjBy_eq_of_mem_normalizer hgN]
      exact hXM
    rcases theorem_10_1_a hM hpσ hXne hXp hXM hXgM with ⟨m, c, hg⟩
    have hcN : (c : G) ∈ Subgroup.normalizer (X : Set G) :=
      centralizer_le_normalizer X c.property
    have hmN : (m : G) ∈ Subgroup.normalizer (X : Set G) := by
      have hm_eq : (m : G) = g * (c : G)⁻¹ := by
        rw [hg]
        simp [mul_assoc]
      rw [hm_eq]
      exact (Subgroup.normalizer (X : Set G)).mul_mem
        hgN ((Subgroup.normalizer (X : Set G)).inv_mem hcN)
    have hmLocal : (m : G) ∈ subgroupNormalizerIn M (X : Set G) :=
      section10_mem_subgroupNormalizerIn.mpr ⟨hmN, m.property⟩
    rw [hg]
    have hmem :
        (m : G) * (c : G) ∈
          subgroupNormalizerIn M (X : Set G) ⊔ Subgroup.centralizer (X : Set G) :=
      Subgroup.mul_mem_sup hmLocal c.property
    simpa using hmem
  · rw [sup_le_iff]
    exact ⟨section10_subgroupNormalizerIn_le_normalizer M (X : Set G),
      centralizer_le_normalizer X⟩

end Section10
