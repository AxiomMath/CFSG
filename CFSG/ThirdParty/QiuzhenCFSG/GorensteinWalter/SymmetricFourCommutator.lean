module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

namespace CFSG
end CFSG
open CFSG

/-!
# The derived subgroup of `S₄`

Every 3-cycle is a commutator of two transpositions.  Since 3-cycles generate
the alternating group, this identifies `[S₄,S₄]` with `A₄`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Equiv
open Equiv.Perm
open scoped commutatorElement

private theorem threeCycle_mem_commutator_perm_four
    (g : Equiv.Perm (Fin 4)) (hg : g.IsThreeCycle) :
    g ∈ commutator (Equiv.Perm (Fin 4)) := by
  have hsupport : g.support.Nonempty := Finset.card_pos.mp (by
    rw [hg.card_support]
    norm_num)
  obtain ⟨a, ha⟩ := hsupport
  let s : Equiv.Perm (Fin 4) := Equiv.swap a (g a)
  let t : Equiv.Perm (Fin 4) := Equiv.swap (g a) (g (g a))
  have hrep : g = s * t := by
    exact (hg.eq_swap_mul_swap_iff_mem_support).2 ha
  have hs : s⁻¹ = s := by simp [s]
  have ht : t⁻¹ = t := by simp [t]
  have hts : t * s = g⁻¹ := by
    rw [hrep, mul_inv_rev, hs, ht]
  have hg3 : g ^ 3 = 1 := by
    rw [← hg.orderOf]
    exact pow_orderOf_eq_one g
  have hpow : (g⁻¹) ^ 2 = g := by
    have hginv : g⁻¹ = g ^ 2 := by
      apply (inv_eq_iff_mul_eq_one).2
      simpa [pow_succ, mul_assoc] using hg3
    rw [hginv, ← pow_mul]
    norm_num
    calc
      g ^ 4 = g ^ (3 + 1) := by norm_num
      _ = g ^ 3 * g ^ 1 := by rw [pow_add]
      _ = g := by rw [hg3]; simp
  have hcomm : ⁅t, s⁆ = g := by
    rw [commutatorElement_def, ht, hs]
    change (t * s) ^ 2 = g
    rw [hts, hpow]
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator
    (show t ∈ (⊤ : Subgroup (Equiv.Perm (Fin 4))) by trivial)
    (show s ∈ (⊤ : Subgroup (Equiv.Perm (Fin 4))) by trivial)

/-- The commutator subgroup of `S₄` is `A₄`. -/
public theorem commutator_perm_fin_four_eq_alternatingGroup :
    commutator (Equiv.Perm (Fin 4)) = alternatingGroup (Fin 4) := by
  apply le_antisymm alternatingGroup.commutator_perm_le
  intro g hg
  let ga : alternatingGroup (Fin 4) := ⟨g, hg⟩
  have hga : ga ∈ Subgroup.closure
      {z : alternatingGroup (Fin 4) |
        (z : Equiv.Perm (Fin 4)).IsThreeCycle} := by
    rw [alternatingGroup.closure_isThreeCycles_eq_top]
    trivial
  change (ga : Equiv.Perm (Fin 4)) ∈ commutator (Equiv.Perm (Fin 4))
  refine Subgroup.closure_induction
    (k := {z : alternatingGroup (Fin 4) |
      (z : Equiv.Perm (Fin 4)).IsThreeCycle})
    (p := fun (z : alternatingGroup (Fin 4)) _ =>
      (z : Equiv.Perm (Fin 4)) ∈ commutator (Equiv.Perm (Fin 4)))
    (x := ga) ?_ ?_ ?_ ?_ hga
  · intro z hz
    exact threeCycle_mem_commutator_perm_four z hz
  · exact (commutator (Equiv.Perm (Fin 4))).one_mem
  · intro x y hx hy hx' hy'
    exact (commutator (Equiv.Perm (Fin 4))).mul_mem hx' hy'
  · intro x hx hx'
    exact (commutator (Equiv.Perm (Fin 4))).inv_mem hx'

end CFSG.GorensteinWalter
