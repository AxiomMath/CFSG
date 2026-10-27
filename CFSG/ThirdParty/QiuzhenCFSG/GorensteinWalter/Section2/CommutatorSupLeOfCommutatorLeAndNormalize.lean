module

public import Mathlib.GroupTheory.Commutator.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Join commutator control under normalization

If each of two subgroups commutes with a third subgroup modulo `D`, and both
normalize `D`, then their join also commutes with the third subgroup modulo
`D`.  This is the reusable join step extracted from the Bender (1970)
double-commutator argument.
-/

noncomputable section

open scoped Pointwise commutatorElement

namespace CFSG.GorensteinWalter

universe u

/-- If `A` and `B` both normalize `D` and both commute with `C` modulo `D`,
then the join of `A` and `B` commutes with `C` modulo `D`. -/
public theorem commutator_sup_le_of_commutator_le_and_normalize
    {G : Type u} [Group G]
    (A B C D : Subgroup G)
    (hAC : ⁅A, C⁆ ≤ D) (hBC : ⁅B, C⁆ ≤ D)
    (hAD : A ≤ Subgroup.normalizer (D : Set G))
    (hBD : B ≤ Subgroup.normalizer (D : Set G)) :
    ⁅A ⊔ B, C⁆ ≤ D := by
  rw [Subgroup.commutator_le]
  intro x hx c hc
  rw [Subgroup.sup_eq_closure] at hx
  have hsupN : A ⊔ B ≤ Subgroup.normalizer (D : Set G) := sup_le hAD hBD
  refine Subgroup.closure_induction (k := ((A : Set G) ∪ (B : Set G)))
    (p := fun y _hy => ⁅y, c⁆ ∈ D) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with hyA | hyB
    · exact hAC (Subgroup.commutator_mem_commutator hyA hc)
    · exact hBC (Subgroup.commutator_mem_commutator hyB hc)
  · simp
  · intro y z _hy _hz hyP hzP
    have hyN : y ∈ Subgroup.normalizer (D : Set G) := hsupN (by
      simpa [Subgroup.sup_eq_closure] using _hy)
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact D.mul_mem (((Subgroup.mem_normalizer_iff.mp hyN) ⁅z, c⁆).1 hzP) hyP
  · intro y _hy hyP
    have hyN : y ∈ Subgroup.normalizer (D : Set G) := hsupN (by
      simpa [Subgroup.sup_eq_closure] using _hy)
    have hyNinv : y⁻¹ ∈ Subgroup.normalizer (D : Set G) :=
      (Subgroup.normalizer (D : Set G)).inv_mem hyN
    have hcyD : ⁅c, y⁆ ∈ D := by
      simpa [commutatorElement_inv] using D.inv_mem hyP
    rw [commutatorElement_inv_left]
    simpa using ((Subgroup.mem_normalizer_iff.mp hyNinv) ⁅c, y⁆).1 hcyD

end CFSG.GorensteinWalter
