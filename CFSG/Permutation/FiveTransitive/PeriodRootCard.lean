module

public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG

namespace FiveTransitive.PeriodRootCard

open Equiv Function MulAction
open scoped BigOperators

variable {X : Type*} [Finite X]

@[expose] abbrev PeriodRoot (g : Perm X) (n : ℕ) := {x : X // minimalPeriod g x = n}

private theorem periodic (g : Perm X) (x : X) : x ∈ periodicPts g := by
  refine ⟨orderOf g, orderOf_pos g, ?_⟩
  change g^[orderOf g] x = x
  rw [g.iterate_eq_pow, pow_orderOf_eq_one]
  rfl

private def rootPerm (g : Perm X) (n : ℕ) : Perm (PeriodRoot g n) where
  toFun x := ⟨g x.val, (minimalPeriod_apply (periodic g x.val)).trans x.property⟩
  invFun x := ⟨g.symm x.val, by
    have h := minimalPeriod_apply (periodic g (g.symm x.val))
    rw [g.apply_symm_apply] at h
    exact h.symm.trans x.property⟩
  left_inv x := Subtype.ext (g.symm_apply_apply x.val)
  right_inv x := Subtype.ext (g.apply_symm_apply x.val)

private theorem root_minimalPeriod (g : Perm X) (n : ℕ) (x : PeriodRoot g n) :
    minimalPeriod (rootPerm g n) x = n := by
  have hc : Semiconj Subtype.val (rootPerm g n) g := fun _ => rfl
  have he : minimalPeriod (rootPerm g n) x = minimalPeriod g x.val := by
    apply minimalPeriod_eq_minimalPeriod_iff.mpr
    intro m
    change ((rootPerm g n)^[m] x = x) ↔ (g^[m] x.val = x.val)
    rw [← hc.iterate_right m x]
    exact Subtype.ext_iff
  exact he.trans x.property

theorem period_dvd_card (g : Perm X) (n : ℕ) : n ∣ Nat.card (PeriodRoot g n) := by
  classical
  let Y := PeriodRoot g n
  let p := rootPerm g n
  let H := Subgroup.zpowers p
  let _ : Fintype Y := Fintype.ofFinite _
  let _ : Fintype (orbitRel.Quotient H Y) := Fintype.ofFinite _
  have ho (x : Y) : Nat.card (orbit H x) = n := by
    have h := MulAction.minimalPeriod_eq_card p x
    change minimalPeriod p x = Fintype.card (orbit H x) at h
    rw [← Nat.card_eq_fintype_card] at h
    exact h.symm.trans (root_minimalPeriod g n x)
  have he : Nat.card Y = ∑ q : orbitRel.Quotient H Y, Nat.card (orbit H q.out) := by
    rw [Nat.card_congr (selfEquivSigmaOrbits H Y)]
    simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]
  rw [he]
  simp_rw [ho]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  exact dvd_mul_left n _

end FiveTransitive.PeriodRootCard

end CFSG
