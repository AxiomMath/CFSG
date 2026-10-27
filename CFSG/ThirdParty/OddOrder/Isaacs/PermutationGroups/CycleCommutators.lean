/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Isaacs, Finite Group Theory — Ch. 8: cycle lemmas for Jordan–Bochert (Lem 8.24, 8.25)

Supporting permutation lemmas (Isaacs pp. 236–238) for the `p`-cycle Jordan
public theorem (Thm 8.23) and Bochert's theorem (Thm 8.26):

* **Lem 8.24** (`centralizer_eq_zpowers_of_isCycle_of_support_eq_univ`):
  the centralizer of an `n`-cycle in `Sym(n)` is the cyclic group it
  generates — stated for a cycle with full support on a finite type;
* **Lem 8.25** (`isThreeCycle_commutator_of_unique_common_moved`): if
  exactly one point is moved by both permutations `x` and `y`, then the
  commutator `⁅x, y⁆` is a `3`-cycle.
-/

public section

namespace CFSG

namespace FiveTransitive.OddOrder.Isaacs.Ch08

open Equiv Equiv.Perm

open scoped commutatorElement

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [DecidableEq α] [Fintype α] in
/-- `f (f⁻¹ b) = b` for a permutation, stated for `⁻¹` rather than `symm`. -/
private lemma perm_apply_inv_self (f : Perm α) (b : α) : f (f⁻¹ b) = b :=
  f.apply_symm_apply b

omit [DecidableEq α] [Fintype α] in
/-- `f⁻¹ (f b) = b` for a permutation, stated for `⁻¹` rather than `symm`. -/
private lemma perm_inv_apply_self (f : Perm α) (b : α) : f⁻¹ (f b) = b :=
  f.symm_apply_apply b

/-! ### Isaacs Lem 8.24 -/

/-- **Isaacs Lem 8.24** — the centralizer of an `n`-cycle in `Sym(n)` is the
cyclic group it generates: for a cycle `c` with full support,
`C(c) = ⟨c⟩`.  (The proof is via `Equiv.Perm.IsCycle.commute_iff` rather
than Isaacs's class-counting argument.) -/
theorem centralizer_eq_zpowers_of_isCycle_of_support_eq_univ
    {c : Perm α} (hc : c.IsCycle) (hsupp : c.support = Finset.univ) :
    Subgroup.centralizer {c} = Subgroup.zpowers c := by
  apply le_antisymm
  · intro z hz
    have hcomm : Commute z c :=
      (Subgroup.mem_centralizer_iff.mp hz c rfl).symm
    obtain ⟨hinv, hmem⟩ := hc.commute_iff.mp hcomm
    have hz' : ofSubtype (z.subtypePerm hinv) = z := by
      ext b
      have hb : b ∈ c.support := hsupp ▸ Finset.mem_univ b
      rw [ofSubtype_apply_of_mem (z.subtypePerm hinv) hb]
      rfl
    rwa [hz'] at hmem
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr fun h hh =>
      (Set.mem_singleton_iff.mp hh) ▸ rfl

/-! ### Isaacs Lem 8.25 -/

section Commutator

variable {x y : Perm α} {a : α}

omit [DecidableEq α] [Fintype α] in
/-- **Isaacs Lem 8.25**, support computation — if exactly one point `a` is
moved by both `x` and `y`, the commutator `⁅x, y⁆` carries
`a ↦ x a ↦ y a ↦ a` and fixes every other point. -/
private lemma commutator_apply_of_unique_common_moved
    (hxa : x a ≠ a) (hya : y a ≠ a)
    (huniq : ∀ b : α, b ≠ a → x b = b ∨ y b = b) :
    ⁅x, y⁆ a = x a ∧ ⁅x, y⁆ (x a) = y a ∧ ⁅x, y⁆ (y a) = a ∧
      ∀ b : α, b ≠ a → b ≠ x a → b ≠ y a → ⁅x, y⁆ b = b := by
  have hinv_ne : ∀ (f : Perm α) (b : α), f b ≠ b → f⁻¹ b ≠ b := fun f b h h2 =>
    h ((congrArg f h2).symm.trans (perm_apply_inv_self f b))
  have hfix_inv : ∀ (f : Perm α) (b : α), f b = b → f⁻¹ b = b := fun f b h =>
    f.symm_apply_eq.mpr h.symm
  have happly : ∀ b : α, ⁅x, y⁆ b = x (y (x⁻¹ (y⁻¹ b))) := fun b => by
    rw [commutatorElement_def]
    simp only [Perm.mul_apply]
  -- `x` moves `x a` and `y` moves `y a`, so the cross-images are fixed
  have hyxa : y (x a) = x a :=
    (huniq (x a) hxa).resolve_left fun h => hxa (x.injective h)
  have hxya : x (y a) = y a :=
    (huniq (y a) hya).resolve_right fun h => hya (y.injective h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `⁅x,y⁆ a = x a`
    rw [happly]
    have h1 : y⁻¹ a ≠ a := hinv_ne y a hya
    have h2 : y (y⁻¹ a) ≠ y⁻¹ a := by
      rw [perm_apply_inv_self y]
      exact Ne.symm h1
    have h3 : x (y⁻¹ a) = y⁻¹ a := (huniq _ h1).resolve_right h2
    rw [hfix_inv x _ h3, perm_apply_inv_self y]
  · -- `⁅x,y⁆ (x a) = y a`
    rw [happly, hfix_inv y _ hyxa, perm_inv_apply_self x, hxya]
  · -- `⁅x,y⁆ (y a) = a`
    rw [happly, perm_inv_apply_self y]
    have h1 : x⁻¹ a ≠ a := hinv_ne x a hxa
    have h2 : x (x⁻¹ a) ≠ x⁻¹ a := by
      rw [perm_apply_inv_self x]
      exact Ne.symm h1
    have h3 : y (x⁻¹ a) = x⁻¹ a := (huniq _ h1).resolve_left h2
    rw [h3, perm_apply_inv_self x]
  · -- all other points are fixed
    intro b hba hbxa hbya
    rw [happly]
    by_cases hxb : x b = b
    · by_cases hyb : y b = b
      · rw [hfix_inv y _ hyb, hfix_inv x _ hxb, hyb, hxb]
      · -- `y` moves `b`, `x` fixes `b` and `y⁻¹ b`
        have h1 : y⁻¹ b ≠ b := hinv_ne y b hyb
        have h1a : y⁻¹ b ≠ a := fun h => hbya (by rw [← h, perm_apply_inv_self y])
        have h2 : y (y⁻¹ b) ≠ y⁻¹ b := by
          rw [perm_apply_inv_self y]
          exact Ne.symm h1
        have h3 : x (y⁻¹ b) = y⁻¹ b := (huniq _ h1a).resolve_right h2
        rw [hfix_inv x _ h3, perm_apply_inv_self y, hxb]
    · -- `x` moves `b`, so `y` fixes `b` and `x⁻¹ b`
      have hyb : y b = b := (huniq b hba).resolve_left hxb
      have h1 : x⁻¹ b ≠ b := hinv_ne x b hxb
      have h1a : x⁻¹ b ≠ a := fun h => hbxa (by rw [← h, perm_apply_inv_self x])
      have h2 : x (x⁻¹ b) ≠ x⁻¹ b := by
        rw [perm_apply_inv_self x]
        exact Ne.symm h1
      have h3 : y (x⁻¹ b) = x⁻¹ b := (huniq _ h1a).resolve_left h2
      rw [hfix_inv y _ hyb, h3, perm_apply_inv_self x]

/-- **Isaacs Lem 8.25** — if exactly one point is moved by both permutations
`x` and `y`, then their commutator is a `3`-cycle. -/
theorem isThreeCycle_commutator_of_unique_common_moved
    (hxa : x a ≠ a) (hya : y a ≠ a)
    (huniq : ∀ b : α, b ≠ a → x b = b ∨ y b = b) :
    (⁅x, y⁆ : Perm α).IsThreeCycle := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    commutator_apply_of_unique_common_moved hxa hya huniq
  have hxya : x a ≠ y a := by
    intro h
    have hyxa : y (x a) = x a :=
      (huniq (x a) hxa).resolve_left fun h2 => hxa (x.injective h2)
    rw [h] at hyxa
    exact hya (y.injective hyxa)
  have hsupp : (⁅x, y⁆ : Perm α).support = {a, x a, y a} := by
    ext b
    simp only [mem_support, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hb
      by_contra hnot
      simp only [not_or] at hnot
      exact hb (h4 b hnot.1 hnot.2.1 hnot.2.2)
    · rintro (rfl | rfl | rfl)
      · rw [h1]; exact hxa
      · rw [h2]; exact Ne.symm hxya
      · rw [h3]; exact Ne.symm hya
  have hcard : (⁅x, y⁆ : Perm α).support.card = 3 := by
    rw [hsupp, Finset.card_insert_of_notMem (by simp [Ne.symm hxa, Ne.symm hya]),
      Finset.card_insert_of_notMem (by simp [hxya]), Finset.card_singleton]
  exact card_support_eq_three_iff.mp hcard

end Commutator

end FiveTransitive.OddOrder.Isaacs.Ch08

end CFSG
