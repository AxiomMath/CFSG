module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_1_b
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Theorem 10.1(a) from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Theorem 10.1(a).  With `Subgroup.conjBy` as left conjugation,
`X.conjBy g ≤ M` gives the book's double-coset conclusion in the order
`M * C_G(X)`. -/
public theorem CFSG.theorem_10_1_a
    {M X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpσ : p ∈ section10SigmaPrimes M)
    (hXne : X ≠ ⊥) (hXp : IsPGroup p.val X) (hXM : X ≤ M) {g : G}
    (hXgM : X.conjBy g ≤ M) :
    ∃ m : M, ∃ c : Subgroup.centralizer (X : Set G), g = (m : G) * (c : G) := by
  classical
  have htrans := theorem_10_1_b hM hpσ hXne hXp hXM
  have hMnorm : Subgroup.normalizer (M : Set G) = M :=
    section10_maximal_normalizer_eq_self_of_sigma hM hpσ
  have hX_le_Mginv : X ≤ M.conjBy g⁻¹ := by
    intro x hx
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨g * x * g⁻¹, ?_, ?_⟩
    · apply hXgM
      rw [Subgroup.conjBy, Subgroup.mem_map]
      exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    · simp [mul_assoc]
  have hMginv_mem : M.conjBy g⁻¹ ∈ section10ConjugatesContaining M X :=
    ⟨g⁻¹, rfl, hX_le_Mginv⟩
  have hM_mem : M ∈ section10ConjugatesContaining M X :=
    ⟨1, (section10_conjBy_one M).symm, hXM⟩
  rcases htrans (M.conjBy g⁻¹) hMginv_mem M hM_mem with ⟨c, hc⟩
  have hcgnorm : (c : G) * g⁻¹ ∈ Subgroup.normalizer (M : Set G) := by
    apply section10_mem_normalizer_of_conjBy_eq
    calc
      M.conjBy ((c : G) * g⁻¹) = (M.conjBy g⁻¹).conjBy (c : G) :=
        section10_conjBy_mul M (c : G) g⁻¹
      _ = M := hc.symm
  have hcgM : (c : G) * g⁻¹ ∈ M := by
    simpa [hMnorm] using hcgnorm
  refine ⟨⟨((c : G) * g⁻¹)⁻¹, M.inv_mem hcgM⟩, c, ?_⟩
  simp [mul_assoc]

end Section10
