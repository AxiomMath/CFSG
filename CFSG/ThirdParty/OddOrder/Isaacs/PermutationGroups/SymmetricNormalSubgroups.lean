/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Index

/-!
# Isaacs, Finite Group Theory — Ch. 8: the normal subgroups of `Sym Ω` (Cor 8.28)

Formalizes **Isaacs Cor 8.28** (p. 240): for `n ≥ 5` the symmetric group `Sₙ` has exactly three
normal subgroups — the identity, the alternating group and the whole group.

Isaacs derives it from **Thm 8.27** (`Aₙ` is simple for `n ≥ 5`), which is mathlib's
`alternatingGroup.isSimpleGroup`.  The audit of issue 0176 found (8.28) to be the *only* one of the
thirteen zero-cite Ch. 8 results with no counterpart in either mathlib or this repository; the
other twelve are mathlib-covered, and the correspondence is tabulated in
`notes/isaacs/ch08_permutation.md`.

The proof needs `Z(Sym Ω) = 1`, which is also absent from mathlib (mathlib's
`Equiv.Perm.alternatingGroup.center_eq_bot` is the centre of the *alternating* group), so it is
proved here first as `center_perm_eq_bot`.
-/

public section

namespace CFSG

namespace FiveTransitive.OddOrder.Isaacs.Ch08

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

section /- 8E: the normal subgroups of the symmetric group (pp. 239-240) -/

omit [DecidableEq α] in
/-- **`Z(Sym Ω) = 1`** whenever `|Ω| ≥ 3`.  (Not in mathlib: `alternatingGroup.center_eq_bot` is
the centre of the alternating group.)

If a central `t` moved `a` to `b ≠ a`, pick `c ∉ {a, b}` (possible since `|Ω| ≥ 3`) and let
`σ = (b c)`.  Centrality gives `t (σ a) = σ (t a)`; the left side is `t a = b` because `σ` fixes
`a`, and the right side is `σ b = c`.  So `b = c`, contradicting `c ∉ {a, b}`. -/
theorem center_perm_eq_bot (hα : 3 ≤ Fintype.card α) :
    Subgroup.center (Perm α) = ⊥ := by
  classical
  refine (Subgroup.eq_bot_iff_forall _).mpr fun t ht => ?_
  rw [Subgroup.mem_center_iff] at ht
  by_contra htne
  -- `t ≠ 1` moves some point `a`; set `b = t a ≠ a`
  obtain ⟨a, hta⟩ : ∃ a : α, t a ≠ a := by
    by_contra hno
    push Not at hno
    exact htne (Equiv.ext hno)
  -- a third point `c ∉ {a, t a}` exists because `|Ω| ≥ 3`
  obtain ⟨c, hca, hcb⟩ : ∃ c : α, c ≠ a ∧ c ≠ t a := by
    by_contra hno
    push Not at hno
    have hsub : (Finset.univ : Finset α) ⊆ {a, t a} := by
      intro x _
      rcases eq_or_ne x a with rfl | hxa
      · simp
      · simp [hno x hxa]
    have h1 := Finset.card_le_card hsub
    have h2 : ({a, t a} : Finset α).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    rw [Finset.card_univ] at h1
    omega
  -- `t` commutes with the transposition `(t a, c)`
  have happ : (Equiv.swap (t a) c) (t a) = t ((Equiv.swap (t a) c) a) :=
    congrArg (fun f : Perm α => f a) (ht (Equiv.swap (t a) c))
  rw [Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne (fun h => hta h.symm) (fun h => hca h.symm)] at happ
  exact hcb happ

/-- **Isaacs Cor 8.28** (p. 240): for `|Ω| ≥ 5` the only normal subgroups of `Sym Ω` are `1`,
`Alt Ω` and `Sym Ω`.

Write `A = Alt Ω`.  Since `N ⊴ Sym Ω`, the subgroup `N.subgroupOf A` is normal in `A`, which is
simple (`alternatingGroup.isSimpleGroup`, = Isaacs Thm 8.27), so it is `⊥` or `⊤`.

* `⊤` means `A ≤ N`.  As `[Sym Ω : A] = 2` is prime (`alternatingGroup.index_eq_two`), the only
  subgroups between `A` and `Sym Ω` are those two, so `N = A` or `N = ⊤`.
* `⊥` means `N ⊓ A = 1`, i.e. `sign` is injective on `N` (two elements of `N` with the same sign
  differ by an element of `N ⊓ A`).  For `t ∈ N` and any `g`, the conjugate `g t g⁻¹` lies in `N`
  and has the same sign as `t` (`ℤˣ` is commutative), so `g t g⁻¹ = t`: every `t ∈ N` is central.
  By `center_perm_eq_bot` that forces `N = ⊥`. -/
theorem normal_perm_eq_bot_or_alternating_or_top (hα : 5 ≤ Fintype.card α)
    (N : Subgroup (Perm α)) [N.Normal] :
    N = ⊥ ∨ N = alternatingGroup α ∨ N = ⊤ := by
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hsimple : IsSimpleGroup (alternatingGroup α) :=
    alternatingGroup.isSimpleGroup (by rwa [Nat.card_eq_fintype_card])
  have : (N.subgroupOf (alternatingGroup α)).Normal := Subgroup.Normal.subgroupOf ‹N.Normal› _
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup α)) with
    hbot | htop
  · -- `N ⊓ A = 1`: `sign` separates the elements of `N`, so `N ≤ Z(Sym Ω) = 1`.
    left
    have hinter : ∀ x ∈ N, x ∈ alternatingGroup α → x = 1 := by
      intro x hxN hxA
      have : (⟨x, hxA⟩ : alternatingGroup α) ∈ N.subgroupOf (alternatingGroup α) := hxN
      rw [hbot, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    have hsep : ∀ x ∈ N, ∀ y ∈ N, sign x = sign y → x = y := by
      intro x hx y hy hxy
      have hmem : x * y⁻¹ ∈ N := N.mul_mem hx (N.inv_mem hy)
      have hsgn : x * y⁻¹ ∈ alternatingGroup α := by
        rw [mem_alternatingGroup, map_mul, map_inv, hxy]
        exact mul_inv_cancel _
      have := hinter _ hmem hsgn
      rwa [mul_inv_eq_one] at this
    refine (Subgroup.eq_bot_iff_forall _).mpr fun t ht => ?_
    have hcentral : t ∈ Subgroup.center (Perm α) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hconj : g * t * g⁻¹ ∈ N := ‹N.Normal›.conj_mem t ht g
      have : g * t * g⁻¹ = t := by
        refine hsep _ hconj _ ht ?_
        simp only [map_mul, map_inv]
        rw [mul_comm (sign g) (sign t), mul_assoc, mul_inv_cancel, mul_one]
      calc g * t = g * t * g⁻¹ * g := by group
        _ = t * g := by rw [this]
    rw [center_perm_eq_bot (by omega), Subgroup.mem_bot] at hcentral
    exact hcentral
  · -- `A ≤ N`, and `[Sym Ω : A] = 2` leaves only `N = A` and `N = ⊤`.
    have hAN : alternatingGroup α ≤ N := by
      intro x hxA
      have : (⟨x, hxA⟩ : alternatingGroup α) ∈ N.subgroupOf (alternatingGroup α) := by
        rw [htop]; trivial
      exact this
    have hidx : (alternatingGroup α).index = 2 := alternatingGroup.index_eq_two
    have hmul : (alternatingGroup α).relIndex N * N.index = 2 := by
      rw [Subgroup.relIndex_mul_index hAN, hidx]
    -- `2` is prime, so the relative index is `1` (giving `N = A`) or `2` (giving `N = ⊤`).
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ ⟨N.index, hmul.symm⟩ with hrel | hrel
    · exact Or.inr (Or.inl ((Subgroup.relIndex_eq_one.mp hrel).antisymm hAN))
    · refine Or.inr (Or.inr (Subgroup.index_eq_one.mp ?_))
      rw [hrel] at hmul
      omega

end

end FiveTransitive.OddOrder.Isaacs.Ch08

end CFSG
