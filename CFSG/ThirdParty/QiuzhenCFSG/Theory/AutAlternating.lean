module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

namespace CFSG
end CFSG
open CFSG

/-!
# Automorphisms of the alternating groups

This module formalises **GLS vol. 3, Theorem 5.2.1**: for `n ≥ 5` and `n ≠ 6`,
every automorphism of the alternating group `Aₙ` is conjugation by an element of
the symmetric group `Sₙ` — the conjugation map `Sₙ → Aut(Aₙ)` is bijective.  (The
case `n = 6` is genuinely exceptional: `Out(A₆)` is a four-group.)  This is the
alternating arm of the Schreier property for known simple groups (GLS vol. 3,
Theorem 7.1.1(a)).

The classical proof, following Suzuki [Sul, pp. 299–301]:

* **Injectivity**: an element of `Sₙ` centralizing `Aₙ` commutes with every
  3-cycle, hence preserves every three-element support, which forces it to be the
  identity (`n ≥ 4`).
* **Surjectivity**: an automorphism `φ` of `Aₙ` maps the conjugacy class of
  3-cycles to itself (`n ≥ 5`, `n ≠ 6`); two distinct 3-cycles `c ≠ c'` have
  `orderOf (c * c') = 2` exactly when they share two points, a relation preserved
  by `φ`; the images of the 3-cycles through a common point share a common point,
  defining a permutation `σ` of the underlying set with
  `φ ((i j k)) = (σ(i) σ(j) σ(k))`, so `φ` is conjugation by `σ`.

Both halves are proved here (`conjNormal_injective_alternatingGroup` and
`aut_alternatingGroup_bijective_conj`).
-/

universe u

noncomputable section

namespace CFSG.GroupTheory

namespace AutAlternating

open Equiv
open Equiv.Perm

/-- `IsThreeCycle` is decidable: it is the multiset equality `cycleType = {3}`. -/
local instance decidableIsThreeCycle (α : Type*) [Fintype α] [DecidableEq α] :
    DecidablePred (fun σ : Perm α => σ.IsThreeCycle) :=
  fun σ => (inferInstance : Decidable (σ.cycleType = {3}))

/-! ### Conjugation of transpositions and 3-cycles -/

/-- Conjugating a transposition by a permutation moves its two points. -/
public theorem conj_swap {α : Type*} [DecidableEq α] (σ : Equiv.Perm α) (a b : α) :
    σ * Equiv.swap a b * σ⁻¹ = Equiv.swap (σ a) (σ b) := by
  ext x
  by_cases hxa : x = σ a
  · subst hxa
    simp [Equiv.symm_apply_apply]
  by_cases hxb : x = σ b
  · subst hxb
    simp [Equiv.symm_apply_apply]
  · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
    have hx' : σ⁻¹ x ≠ a := by
      intro h
      apply hxa
      rw [← h]
      simp
    have hx'' : σ⁻¹ x ≠ b := by
      intro h
      apply hxb
      rw [← h]
      simp
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hx' hx'']
    simp

/-- The support of the 3-cycle `(i j k)`, realized as `swap i j * swap i k`, is
`{i, j, k}`. -/
public theorem support_swap_mul_swap_same {α : Type*} [Fintype α] [DecidableEq α]
    {i j k : α} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    support (Equiv.swap i j * Equiv.swap i k) = {i, j, k} := by
  apply le_antisymm ((support_mul_le _ _).trans ?_) ?_
  · rw [support_swap hij, support_swap hik]
    simp
  · intro x hx
    rw [mem_support]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hxi | hxj | hxk
    · -- x = i
      rw [hxi]
      have : (Equiv.swap i j * Equiv.swap i k) i = k := by
        simp [Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm]
      rw [this]
      exact hik.symm
    · -- x = j
      rw [hxj]
      have : (Equiv.swap i j * Equiv.swap i k) j = i := by
        simp [Equiv.swap_apply_of_ne_of_ne hij.symm hjk]
      rw [this]
      exact hij
    · -- x = k
      rw [hxk]
      have : (Equiv.swap i j * Equiv.swap i k) k = j := by
        simp
      rw [this]
      exact hjk

/-! ### The centralizer of `Aₙ` in `Sₙ` -/

/-- In a type with at least four elements, three points distinct from a given point
and from each other exist. -/
private theorem exists_three_ne_of_card {α : Type*} [Fintype α] [DecidableEq α]
    (h : 4 ≤ Fintype.card α) (i : α) :
    ∃ j k l : α, i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l := by
  classical
  have hcard : 3 ≤ (Finset.univ.erase i).card := by
    have h' := Finset.card_erase_add_one (s := Finset.univ) (a := i) (Finset.mem_univ i)
    rw [Finset.card_univ] at h'
    omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.erase i).card)
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hcard₂ : 2 ≤ ((Finset.univ.erase i).erase j).card := by
    have h' := Finset.card_erase_add_one (s := Finset.univ.erase i) (a := j) hj
    omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp (by omega : 0 < ((Finset.univ.erase i).erase j).card)
  have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
  have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  have hcard₁ : 1 ≤ (((Finset.univ.erase i).erase j).erase k).card := by
    have h' := Finset.card_erase_add_one (s := (Finset.univ.erase i).erase j) (a := k) hk
    omega
  obtain ⟨l, hl⟩ := Finset.card_pos.mp (by omega : 0 < (((Finset.univ.erase i).erase j).erase k).card)
  have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
  have hlj : l ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
  have hli : l ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).2).1
  exact ⟨j, k, l, hji.symm, hki.symm, hli.symm, hkj.symm, hlj.symm, hlk.symm⟩

/-- An element of the symmetric group centralizing the alternating group preserves
the support of every 3-cycle, hence of every three-element set. -/
private theorem map_three_subset_eq_of_mem_centralizer {α : Type*} [Fintype α] [DecidableEq α]
    (x : Perm α) (hx : x ∈ Subgroup.centralizer ((alternatingGroup α : Subgroup (Perm α)) : Set (Perm α)))
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset α).map x.toEmbedding = {a, b, c} := by
  -- the 3-cycle `swap a b * swap a c` lies in `Aₙ`, so `x` commutes with it; its
  -- support is preserved
  have hc : IsThreeCycle (Equiv.swap a b * Equiv.swap a c) :=
    isThreeCycle_swap_mul_swap_same hab hac hbc
  have hcA : Equiv.swap a b * Equiv.swap a c ∈ alternatingGroup α := hc.mem_alternatingGroup
  have hcomm : x * (Equiv.swap a b * Equiv.swap a c) =
      (Equiv.swap a b * Equiv.swap a c) * x :=
    (Subgroup.mem_centralizer_iff.mp hx (Equiv.swap a b * Equiv.swap a c) hcA).symm
  have hxcx : x * (Equiv.swap a b * Equiv.swap a c) * x⁻¹ =
      Equiv.swap a b * Equiv.swap a c := by
    calc
      x * (Equiv.swap a b * Equiv.swap a c) * x⁻¹ =
          (Equiv.swap a b * Equiv.swap a c) * x * x⁻¹ := by rw [← hcomm]
      _ = Equiv.swap a b * Equiv.swap a c := by simp [mul_assoc]
  have hsup : (x * (Equiv.swap a b * Equiv.swap a c) * x⁻¹).support =
      (Equiv.swap a b * Equiv.swap a c).support := by rw [hxcx]
  rw [support_conj] at hsup
  rw [← support_swap_mul_swap_same hab hac hbc]
  exact hsup

/-- The centralizer of the alternating group in the symmetric group is trivial for
`n ≥ 4`.  An element commuting with `Aₙ` commutes with every 3-cycle, hence
preserves every three-element support, hence fixes each point. -/
public theorem centralizer_alternatingGroup_eq_bot (n : ℕ) (hn : 4 ≤ n) :
    Subgroup.centralizer ((alternatingGroup (Fin n) : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) =
      ⊥ := by
  apply le_antisymm
  · intro x hx
    apply (Subgroup.mem_bot).2
    ext i
    obtain ⟨j, k, l, hij, hik, hil, hjk, hjl, hkl⟩ :=
      exists_three_ne_of_card (α := Fin n) (by simpa using hn) i
    have hx₁ : x i ∈ ({i, j, k} : Finset (Fin n)) := by
      have hmap := map_three_subset_eq_of_mem_centralizer (α := Fin n) x hx hij hik hjk
      have hxmem : x i ∈ ({i, j, k} : Finset (Fin n)).map x.toEmbedding :=
        (Finset.mem_map).2 ⟨i, by simp, rfl⟩
      rwa [hmap] at hxmem
    have hx₂ : x i ∈ ({i, j, l} : Finset (Fin n)) := by
      have hmap := map_three_subset_eq_of_mem_centralizer (α := Fin n) x hx hij hil hjl
      have hxmem : x i ∈ ({i, j, l} : Finset (Fin n)).map x.toEmbedding :=
        (Finset.mem_map).2 ⟨i, by simp, rfl⟩
      rwa [hmap] at hxmem
    have hx₃ : x i ∈ ({i, k, l} : Finset (Fin n)) := by
      have hmap := map_three_subset_eq_of_mem_centralizer (α := Fin n) x hx hik hil hkl
      have hxmem : x i ∈ ({i, k, l} : Finset (Fin n)).map x.toEmbedding :=
        (Finset.mem_map).2 ⟨i, by simp, rfl⟩
      rwa [hmap] at hxmem
    have hxmem : x i ∈ ({i, j, k} ∩ {i, j, l} ∩ {i, k, l} : Finset (Fin n)) := by
      rw [Finset.mem_inter, Finset.mem_inter]
      exact ⟨⟨hx₁, hx₂⟩, hx₃⟩
    have hxeq : ({i, j, k} ∩ {i, j, l} ∩ {i, k, l} : Finset (Fin n)) = {i} := by
      ext a
      simp [hij, hik, hil, hjk, hjl, hkl]
    have hxi : x i = i := by
      rwa [hxeq, Finset.mem_singleton] at hxmem
    simp [hxi]
  · exact bot_le

/-! ### Milestone 3: automorphisms preserve the class of 3-cycles -/

/-- An element of order `3` has cycle type `3^r` for some `r ≥ 1`: its cycles are
exactly `r` disjoint 3-cycles. -/
private theorem cycleType_of_order_three {α : Type*} [Fintype α] [DecidableEq α] (g : Perm α)
    (hg : orderOf g = 3) : ∃ r : ℕ, 1 ≤ r ∧ g.cycleType = Multiset.replicate r 3 := by
  have hp : (orderOf g).Prime := by rw [hg]; exact Nat.prime_three
  obtain ⟨k, hk⟩ := cycleType_prime_order (σ := g) hp
  refine ⟨k + 1, by omega, ?_⟩
  simpa [hg] using hk

/-- `∏ i ∈ range n, (i+1) = n!`. -/
private theorem prod_range_succ_eq_factorial (n : ℕ) :
    (∏ i ∈ Finset.range n, (i + 1)) = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ]
      rw [ih, Nat.factorial_succ]
      ring

/-- `(k+3)! = (k+3)(k+2)(k+1)k!`. -/
private theorem factorial_add_three (k : ℕ) :
    (k + 3).factorial = (k + 3) * (k + 2) * (k + 1) * k.factorial := by
  rw [show k + 3 = (k + 2) + 1 by omega, Nat.factorial_succ]
  rw [show k + 2 = (k + 1) + 1 by omega, Nat.factorial_succ]
  rw [show k + 1 = k + 1 by rfl, Nat.factorial_succ]
  ring

/-- `3 · #(3-cycles) = n(n-1)(n-2)` on `n` points. -/
private theorem card_threeCycle (n : ℕ) (hn : 3 ≤ n) :
    3 * (Finset.univ.filter fun g : Perm (Fin n) => g.IsThreeCycle).card = n * (n - 1) * (n - 2) := by
  classical
  have h₁ : (Finset.univ.filter fun g : Perm (Fin n) => g.IsThreeCycle) =
      (Finset.univ.filter fun g : Perm (Fin n) => g.cycleType = {3}) := by
    ext g
    rfl
  rw [h₁]
  have h₂ : (Finset.univ.filter fun g : Perm (Fin n) => g.cycleType = {3}).card =
      (3 - 1).factorial * n.choose 3 := by
    simpa [Fintype.card_fin] using
      (Equiv.Perm.card_of_cycleType_singleton (α := Fin n) (n := 3) (by norm_num)
        (by simpa [Fintype.card_fin] using hn))
  rw [h₂]
  -- 6·C(n,3) = n(n-1)(n-2)
  have h6 : 6 * n.choose 3 = n * (n - 1) * (n - 2) := by
    apply Nat.mul_right_cancel (Nat.factorial_pos (n - 3))
    calc
      6 * n.choose 3 * (n - 3).factorial = n.choose 3 * (3 : ℕ).factorial * (n - 3).factorial := by
        norm_num [Nat.factorial]
        exact Or.inl (by ring)
      _ = n.factorial := Nat.choose_mul_factorial_mul_factorial (k := 3) (n := n) hn
      _ = n * (n - 1) * (n - 2) * (n - 3).factorial := by
        rw [show n = (n - 3) + 3 by omega, factorial_add_three]
        congr 1
  calc
    3 * ((3 - 1).factorial * n.choose 3) = 6 * n.choose 3 := by
      norm_num [Nat.factorial]
      ring
    _ = n * (n - 1) * (n - 2) := h6

/-- The size of the `Sₙ`-conjugacy class of an element of cycle type `3^r` times
`(n-3r)! · 3^r · r!` is `n!`. -/
private theorem card_isConj_replicate (n r : ℕ) {y : Perm (Fin n)}
    (hy : y.cycleType = Multiset.replicate r 3) :
    Fintype.card {h : Perm (Fin n) // IsConj y h} * ((n - 3 * r).factorial * 3 ^ r * r.factorial) =
      n.factorial := by
  classical
  have hsum : y.cycleType.sum = 3 * r := by
    rw [hy, Multiset.sum_replicate]
    simp [mul_comm]
  have hprod : y.cycleType.prod = 3 ^ r := by
    rw [hy, Multiset.prod_replicate]
  have hfac : (∏ n ∈ y.cycleType.toFinset, (y.cycleType.count n).factorial) = r.factorial := by
    rw [hy]
    by_cases hr : r = 0
    · subst hr
      simp
    · have hto : (Multiset.replicate r 3).toFinset = ({3} : Finset ℕ) := by
        rw [Multiset.toFinset_replicate, if_neg hr]
      rw [hto]
      simp [Multiset.count_replicate]
  have hc := Equiv.Perm.card_isConj_mul_eq (α := Fin n) y
  simpa [hsum, hprod, hfac, Nat.card_eq_fintype_card, Fintype.card_fin,
    Fintype.card_subtype, mul_assoc, mul_comm, mul_left_comm] using hc

/-- The `Aₙ`-conjugacy class of `y` is at least half as large as its `Sₙ`-conjugacy
class: the latter splits into at most two classes on restriction to `Aₙ`. -/
private theorem card_class_A_ge_half {n : ℕ} (hn : 5 ≤ n) (y : alternatingGroup (Fin n)) :
    Fintype.card {h : Perm (Fin n) // IsConj (y : Perm (Fin n)) h} ≤
      2 * Fintype.card {z : alternatingGroup (Fin n) // IsConj y z} := by
  classical
  have : NeZero n := ⟨by omega⟩
  let τ : Perm (Fin n) := Equiv.swap 0 1
  -- the set of conjugates of `y` by elements of `Aₙ`, viewed in `Sₙ`
  let X : Finset (Perm (Fin n)) :=
    Finset.univ.filter fun h : Perm (Fin n) =>
      ∃ a : alternatingGroup (Fin n), h = (a : Perm (Fin n)) * (y : Perm (Fin n)) * (a : Perm (Fin n))⁻¹
  have hX_card : X.card = Fintype.card {z : alternatingGroup (Fin n) // IsConj y z} := by
    -- |X| ≤ |class_A|: send an Aₙ-conjugate to the corresponding class element
    let f : ↥X → {z : alternatingGroup (Fin n) // IsConj y z} := fun h =>
      let a := Classical.choose (Finset.mem_filter.mp h.2).2
      ⟨a * y * a⁻¹, by
        rw [isConj_iff]
        exact ⟨a, rfl⟩⟩
    have hinj_f : Function.Injective f := by
      intro h w hfw
      apply Subtype.ext
      let ah : alternatingGroup (Fin n) := Classical.choose (Finset.mem_filter.mp h.2).2
      let aw : alternatingGroup (Fin n) := Classical.choose (Finset.mem_filter.mp w.2).2
      have hh := Classical.choose_spec (Finset.mem_filter.mp h.2).2
      have hw := Classical.choose_spec (Finset.mem_filter.mp w.2).2
      calc
        (h.1 : Perm (Fin n)) = (ah : Perm (Fin n)) * (y : Perm (Fin n)) * (ah : Perm (Fin n))⁻¹ := by
          simpa [ah] using hh
        _ = (aw : Perm (Fin n)) * (y : Perm (Fin n)) * (aw : Perm (Fin n))⁻¹ := by
          simpa [f, ah, aw] using
            congrArg (fun t : alternatingGroup (Fin n) => (t : Perm (Fin n))) (congrArg Subtype.val hfw)
        _ = (w.1 : Perm (Fin n)) := by
          simpa [aw] using hw.symm
    -- |class_A| ≤ |X|: the coercion is injective
    let g : {z : alternatingGroup (Fin n) // IsConj y z} → ↥X := fun z =>
      ⟨(z : Perm (Fin n)), by
        simp [X]
        rcases (isConj_iff.mp z.2) with ⟨g, hg⟩
        refine ⟨g, ?_⟩
        constructor
        · exact Equiv.Perm.mem_alternatingGroup.mp g.2
        · simpa using congrArg (fun t : alternatingGroup (Fin n) => (t : Perm (Fin n))) hg.symm⟩
    have hinj_g : Function.Injective g := by
      intro z w hzw
      apply Subtype.ext
      exact Subtype.coe_injective (congrArg (fun t : ↥X => (t : Perm (Fin n))) hzw)
    apply le_antisymm
    · exact (Fintype.card_coe X).symm.trans_le (Fintype.card_le_of_injective f hinj_f)
    · exact (Fintype.card_le_of_injective g hinj_g).trans_eq (Fintype.card_coe X)
  -- the Sₙ-class of y is contained in X ∪ τ·X
  have hcover : ({h : Perm (Fin n) | IsConj (y : Perm (Fin n)) h} : Finset (Perm (Fin n))) ⊆
      X ∪ X.image (fun h : Perm (Fin n) => τ * h * τ⁻¹) := by
    intro h hh
    rcases (isConj_iff.mp (Finset.mem_filter.mp hh).2) with ⟨g, hg⟩
    by_cases hsign : sign g = 1
    · -- g ∈ Aₙ: h is an Aₙ-conjugate
      rw [Finset.mem_union]
      left
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨g, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩, ?_⟩
      simp [hg]
    · -- g ∉ Aₙ: g = τ·a with a ∈ Aₙ, and h = τ·(a·y·a⁻¹)·τ⁻¹
      rw [Finset.mem_union]
      right
      rw [Finset.mem_image]
      have hsign' : sign g = -1 := by
        rcases Int.units_eq_one_or (sign g) with h | h
        · exact False.elim (hsign h)
        · exact h
      refine ⟨(τ⁻¹ * g) * (y : Perm (Fin n)) * (τ⁻¹ * g)⁻¹, ?_, ?_⟩
      · simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨⟨τ⁻¹ * g, Equiv.Perm.mem_alternatingGroup.mpr ?_⟩, rfl⟩
        rw [map_mul, map_inv]
        have hτ : sign τ = -1 := by
          rw [sign_swap]
          norm_num
          omega
        rw [hτ, hsign']
        norm_num
      · -- τ * ((τ⁻¹g) · y · (τ⁻¹g)⁻¹) * τ⁻¹ = g · y · g⁻¹ = h
        calc
          τ * ((τ⁻¹ * g) * (y : Perm (Fin n)) * (τ⁻¹ * g)⁻¹) * τ⁻¹ =
              τ * (τ⁻¹ * g) * (y : Perm (Fin n)) * (τ⁻¹ * g)⁻¹ * τ⁻¹ := by
            simp only [mul_assoc]
          _ = (τ * τ⁻¹) * g * (y : Perm (Fin n)) * (τ⁻¹ * g)⁻¹ * τ⁻¹ := by
            simp only [mul_assoc]
          _ = g * (y : Perm (Fin n)) * (τ⁻¹ * g)⁻¹ * τ⁻¹ := by simp
          _ = g * (y : Perm (Fin n)) * (g⁻¹ * τ) * τ⁻¹ := by
            rw [mul_inv_rev]
            simp
          _ = g * (y : Perm (Fin n)) * g⁻¹ * (τ * τ⁻¹) := by
            simp only [mul_assoc]
          _ = g * (y : Perm (Fin n)) * g⁻¹ := by simp
          _ = h := hg
  calc
    Fintype.card {h : Perm (Fin n) // IsConj (y : Perm (Fin n)) h} =
        ({h : Perm (Fin n) | IsConj (y : Perm (Fin n)) h} : Finset (Perm (Fin n))).card := by
      rw [← Fintype.card_subtype (p := fun h : Perm (Fin n) => IsConj (y : Perm (Fin n)) h)]
    _ ≤ (X ∪ X.image (fun h : Perm (Fin n) => τ * h * τ⁻¹)).card := Finset.card_le_card hcover
    _ ≤ X.card + (X.image (fun h : Perm (Fin n) => τ * h * τ⁻¹)).card :=
      Finset.card_union_le X (X.image (fun h : Perm (Fin n) => τ * h * τ⁻¹))
    _ ≤ X.card + X.card := by
      exact Nat.add_le_add_left (Finset.card_image_le) X.card
    _ = 2 * Fintype.card {z : alternatingGroup (Fin n) // IsConj y z} := by
      rw [hX_card, two_mul]

/-- Automorphisms of a group preserve the size of conjugacy classes. -/
private theorem card_class_mulAut_eq {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (φ : MulAut G) (x : G) :
    Fintype.card {z : G // IsConj x z} = Fintype.card {z : G // IsConj (φ x) z} := by
  classical
  exact Fintype.card_congr
    { toFun := fun z => ⟨φ z.1, by
        rcases z with ⟨z, hz⟩
        rw [isConj_iff] at hz ⊢
        rcases hz with ⟨g, hg⟩
        refine ⟨φ g, ?_⟩
        simpa [map_mul, map_inv] using congrArg φ hg⟩
      invFun := fun z => ⟨φ.symm z.1, by
        rcases z with ⟨z, hz⟩
        rw [isConj_iff] at hz ⊢
        rcases hz with ⟨g, hg⟩
        refine ⟨φ.symm g, ?_⟩
        simpa [map_mul, map_inv] using congrArg φ.symm hg⟩
      left_inv := fun z => by ext; simp
      right_inv := fun z => by ext; simp }

/-- The factorial inequality behind the `n ≠ 6` exclusion:
`2 · 3^(r-1) · r! · (n-3r)! < (n-3)!` for `r ≥ 2` and `n ≥ 7`. -/
private theorem factorial_inequality {n r : ℕ} (hn : 7 ≤ n) (hr : 2 ≤ r) (h3r : 3 * r ≤ n) :
    2 * 3 ^ (r - 1) * r.factorial * (n - 3 * r).factorial < (n - 3).factorial := by
  have hsplit : (n - 3).factorial =
      (∏ i ∈ Finset.range (3 * r - 3), (n - 3 * r + i + 1)) * (n - 3 * r).factorial := by
    rw [← prod_range_succ_eq_factorial (n - 3), ← prod_range_succ_eq_factorial (n - 3 * r)]
    rw [show n - 3 = (n - 3 * r) + (3 * r - 3) by omega, Finset.prod_range_add]
    ring
  have htail : (∏ i ∈ Finset.range (3 * r - 3), (n - 3 * r + i + 1)) ≥ (3 * r - 3).factorial := by
    rw [← prod_range_succ_eq_factorial (3 * r - 3)]
    exact Finset.prod_le_prod' (by intro i hi; omega)
  have hpos : 0 < (n - 3 * r).factorial := Nat.factorial_pos (n - 3 * r)
  by_cases h2 : r = 2
  · subst r
    have hsplit2 : (n - 3).factorial = (n - 5) * (n - 4) * (n - 3) * (n - 6).factorial := by
      have hs := hsplit
      rw [show 3 * 2 - 3 = 3 by norm_num] at hs
      rw [hs]
      rw [show (∏ i ∈ Finset.range 3, (n - 3 * 2 + i + 1)) = (n - 5) * (n - 4) * (n - 3) by
        norm_num [Finset.prod_range_succ]
        have h1 : n - 3 * 2 + 1 = n - 5 := by omega
        have h2 : n - 3 * 2 + 1 + 1 = n - 4 := by omega
        rw [h1, h2]
        have h3 : n - 5 + 1 = n - 4 := by omega
        have h4 : n - 4 + 1 = n - 3 := by omega
        rw [h3, h4]]
    have h12 : 12 < (n - 5) * (n - 4) * (n - 3) := by
      have h24 : 24 ≤ (n - 5) * (n - 4) * (n - 3) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega : 2 ≤ n - 5) (by omega : 3 ≤ n - 4))
          (by omega : 4 ≤ n - 3)
      exact lt_of_lt_of_le (by norm_num) h24
    rw [hsplit2]
    rw [show 2 * 3 ^ (2 - 1) * (2 : ℕ).factorial = 12 by norm_num]
    exact Nat.mul_lt_mul_of_pos_right h12 hpos
  · have h3 : 3 ≤ r := by omega
    have hfac : (3 * r - 3).factorial > 2 * 3 ^ (r - 1) * r.factorial := by
      clear h3r hsplit htail hpos h2
      induction r with
      | zero => omega
      | succ r ih =>
          by_cases hr2 : r ≤ 2
          · have hr3 : r + 1 = 3 := by omega
            rw [hr3]
            norm_num [Nat.factorial]
          · have hrm : 3 ≤ r := by omega
            have ih' := ih (by omega : 2 ≤ r) hrm
            have hstep : (3 * r) * (3 * r - 1) * (3 * r - 2) ≥ 3 * (r + 1) := by
              have h₁ : (3 * r - 2) * (3 * r - 1) * (3 * r) ≥ (r + 1) * 3 * 3 := by
                exact Nat.mul_le_mul (Nat.mul_le_mul (by omega : r + 1 ≤ 3 * r - 2) (by omega : 3 ≤ 3 * r - 1)) (by omega : 3 ≤ 3 * r)
              nlinarith [h₁]
            have hrhs : 2 * 3 ^ (r + 1 - 1) * (r + 1).factorial =
                3 * (r + 1) * (2 * 3 ^ (r - 1) * r.factorial) := by
              rw [show r + 1 - 1 = r by omega]
              rw [show r = (r - 1) + 1 by omega, pow_succ]
              rw [Nat.factorial_succ]
              rw [show r - 1 + 1 - 1 = r - 1 by omega]
              ring
            have hleft : (3 * (r + 1) - 3).factorial =
                (3 * r) * (3 * r - 1) * (3 * r - 2) * (3 * r - 3).factorial := by
              rw [show 3 * (r + 1) - 3 = (3 * r - 3) + 3 by omega]
              rw [factorial_add_three]
              congr 3 <;> omega
            rw [hleft, hrhs]
            have hpos' : 0 < (3 * r) * (3 * r - 1) * (3 * r - 2) := by
              exact Nat.mul_pos (Nat.mul_pos (by omega : 0 < 3 * r) (by omega : 0 < 3 * r - 1))
                (by omega : 0 < 3 * r - 2)
            have hmul : (3 * r) * (3 * r - 1) * (3 * r - 2) * (3 * r - 3).factorial >
                (3 * r) * (3 * r - 1) * (3 * r - 2) * (2 * 3 ^ (r - 1) * r.factorial) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                Nat.mul_lt_mul_of_pos_right ih' hpos'
            have hge : (3 * r) * (3 * r - 1) * (3 * r - 2) * (2 * 3 ^ (r - 1) * r.factorial) ≥
                3 * (r + 1) * (2 * 3 ^ (r - 1) * r.factorial) := by
              exact Nat.mul_le_mul hstep le_rfl
            exact lt_of_le_of_lt hge (by simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)
    calc
      2 * 3 ^ (r - 1) * r.factorial * (n - 3 * r).factorial
          < (3 * r - 3).factorial * (n - 3 * r).factorial := Nat.mul_lt_mul_of_pos_right hfac hpos
      _ ≤ (∏ i ∈ Finset.range (3 * r - 3), (n - 3 * r + i + 1)) * (n - 3 * r).factorial :=
          Nat.mul_le_mul_right (n - 3 * r).factorial htail
      _ = (n - 3).factorial := hsplit.symm

/-- The `Aₙ`-conjugacy class of a 3-cycle is no larger than the set of 3-cycles. -/
private theorem card_class_threeCycle_le {n : ℕ} (_hn : 3 ≤ n) (x : alternatingGroup (Fin n))
    (hx : (x : Perm (Fin n)).IsThreeCycle) :
    Fintype.card {z : alternatingGroup (Fin n) // IsConj x z} ≤
      (Finset.univ.filter fun g : Perm (Fin n) => g.IsThreeCycle).card := by
  classical
  -- every conjugate of x is again a 3-cycle
  have hz : ∀ z : alternatingGroup (Fin n), IsConj x z → (z : Perm (Fin n)).IsThreeCycle := by
    intro z hz
    rw [isConj_iff] at hz
    rcases hz with ⟨g, hg⟩
    have hz' : (z : Perm (Fin n)) = (g : Perm (Fin n)) * (x : Perm (Fin n)) * (g : Perm (Fin n))⁻¹ := by
      simpa using congrArg Subtype.val hg.symm
    rw [hz', ← card_support_eq_three_iff]
    rw [support_conj]
    simpa [Finset.card_map] using hx.card_support
  -- the injection z ↦ (z : Perm) into the 3-cycles
  let f : {z : alternatingGroup (Fin n) // IsConj x z} →
      {g : Perm (Fin n) // g.IsThreeCycle} := fun z => ⟨z.1, hz z.1 z.2⟩
  have hinj : Function.Injective f := by
    intro z w hzw
    apply Subtype.ext
    exact Subtype.coe_injective
      (congrArg (fun t : {g : Perm (Fin n) // g.IsThreeCycle} => (t : Perm (Fin n))) hzw)
  rw [Fintype.card_subtype (p := fun z : alternatingGroup (Fin n) => IsConj x z)]
  have hle : Fintype.card {z : alternatingGroup (Fin n) // IsConj x z} ≤
      Fintype.card {g : Perm (Fin n) // g.IsThreeCycle} :=
    Fintype.card_le_of_injective f hinj
  simpa [Fintype.card_subtype] using hle

/-- For `n ≥ 7`, the `Sₙ`-conjugacy class of an element of cycle type `3^r`, `r ≥ 2`,
has more than twice as many elements as there are 3-cycles. -/
private theorem card_class_replicate_gt (n r : ℕ) (hn : 7 ≤ n) (hr : 2 ≤ r) (h3r : 3 * r ≤ n)
    {y : Perm (Fin n)} (hy : y.cycleType = Multiset.replicate r 3) :
    2 * (Finset.univ.filter fun g : Perm (Fin n) => g.IsThreeCycle).card <
      Fintype.card {h : Perm (Fin n) // IsConj y h} := by
  classical
  let T : ℕ := (Finset.univ.filter fun g : Perm (Fin n) => g.IsThreeCycle).card
  let B : ℕ := (n - 3 * r).factorial * 3 ^ r * r.factorial
  let S : ℕ := Fintype.card {h : Perm (Fin n) // IsConj y h}
  -- 3T = n(n-1)(n-2) and S·B = n!
  have hT : 3 * T = n * (n - 1) * (n - 2) := by
    simpa [T] using card_threeCycle n (by omega)
  have hS : S * B = n.factorial := by
    simpa [S, B] using card_isConj_replicate n r hy
  -- the factorial inequality, multiplied by 3·n(n-1)(n-2): 2·P·B < 3·n!
  have hfi := factorial_inequality (n := n) (r := r) (by omega) hr h3r
  have hpow : 3 ^ r = 3 * 3 ^ (r - 1) := by
    rw [show r = (r - 1) + 1 by omega, pow_succ]
    rw [show r - 1 + 1 - 1 = r - 1 by omega]
    ring
  have hn3 : n.factorial = n * (n - 1) * (n - 2) * (n - 3).factorial := by
    rw [show n = (n - 3) + 3 by omega, factorial_add_three]
    have h1 : n - 3 + 3 = n := by omega
    have h2 : n - 3 + 2 = n - 1 := by omega
    have h3 : n - 3 + 1 = n - 2 := by omega
    rw [h1, h2, h3]
  have hPB : 2 * (n * (n - 1) * (n - 2)) * B < 3 * n.factorial := by
    simp only [B]
    have hleft : 2 * (n * (n - 1) * (n - 2)) * ((n - 3 * r).factorial * 3 ^ r * r.factorial) =
        (n * (n - 1) * (n - 2)) * 3 * (2 * 3 ^ (r - 1) * r.factorial * (n - 3 * r).factorial) := by
      rw [hpow]
      ring
    have hright : 3 * n.factorial =
        (n * (n - 1) * (n - 2)) * 3 * (n - 3).factorial := by
      rw [hn3]
      ring
    rw [hleft, hright]
    have hpos' : 0 < (n * (n - 1) * (n - 2)) * 3 := by
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega : 0 < n) (by omega : 0 < n - 1))
        (by omega : 0 < n - 2)) (by norm_num)
    simpa [mul_assoc, mul_left_comm, mul_comm] using Nat.mul_lt_mul_of_pos_right hfi hpos'
  -- 2T < S: 2T·(3B) = 2·(3T)·B = 2PB < 3n! = 3·(S·B) = S·(3B)
  have hmain : 2 * T * (3 * B) < S * (3 * B) := by
    calc
      2 * T * (3 * B) = 2 * (3 * T) * B := by ring
      _ = 2 * (n * (n - 1) * (n - 2)) * B := by rw [hT]
      _ < 3 * n.factorial := hPB
      _ = 3 * (S * B) := by rw [hS]
      _ = S * (3 * B) := by ring
  by_contra h
  have : S * (3 * B) ≤ 2 * T * (3 * B) := Nat.mul_le_mul_right (3 * B) (not_lt.mp h)
  exact (not_lt_of_ge this) hmain

/-- An automorphism of `Aₙ` maps 3-cycles to 3-cycles, for `n ≥ 5`, `n ≠ 6`.  An
automorphism preserves element orders and conjugacy-class sizes; the 3-cycles are
the elements of order 3 whose `Sₙ`-class is the smallest possible. -/
private theorem threeCycle_of_mulAut (n : ℕ) (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (φ : MulAut (alternatingGroup (Fin n))) {c : alternatingGroup (Fin n)}
    (hc : (c : Perm (Fin n)).IsThreeCycle) :
    ((φ c : alternatingGroup (Fin n)) : Perm (Fin n)).IsThreeCycle := by
  classical
  -- φ(c) has order 3
  have horder : orderOf ((φ c : alternatingGroup (Fin n)) : Perm (Fin n)) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hc.orderOf
  -- so it has cycle type 3^r, r ≥ 1
  obtain ⟨r, hr1, hct⟩ :=
    cycleType_of_order_three (g := ((φ c : alternatingGroup (Fin n)) : Perm (Fin n))) horder
  -- |class_A(φ c)| = |class_A(c)| ≤ #(3-cycles)
  have hA : Fintype.card {z : alternatingGroup (Fin n) // IsConj (φ c) z} ≤
      (Finset.univ.filter fun g : Perm (Fin n) => g.IsThreeCycle).card := by
    rw [← card_class_mulAut_eq φ c]
    exact card_class_threeCycle_le (by omega) c hc
  -- if r ≥ 2, the Sₙ-class of φ(c) has size > 2·(#3-cycles), contradicting
  -- |class_S(φ c)| ≤ 2·|class_A(φ c)| ≤ 2·(#3-cycles)
  have hr' : r = 1 := by
    by_contra hrne
    have hr2 : 2 ≤ r := by omega
    have hsup : ((φ c : alternatingGroup (Fin n)) : Perm (Fin n)).support.card = 3 * r := by
      rw [← sum_cycleType, hct, Multiset.sum_replicate]
      simp [mul_comm]
    have h3r : 3 * r ≤ n := by
      calc
        3 * r = ((φ c : alternatingGroup (Fin n)) : Perm (Fin n)).support.card := hsup.symm
        _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
        _ = n := by simp
    have hn7 : 7 ≤ n := by
      have h6 : 6 ≤ n := by
        calc
          6 = 3 * 2 := by norm_num
          _ ≤ 3 * r := Nat.mul_le_mul_left 3 hr2
          _ ≤ n := h3r
      omega
    have hgt : 2 * (Finset.univ.filter fun g : Perm (Fin n) => g.IsThreeCycle).card <
        Fintype.card {h : Perm (Fin n) // IsConj ((φ c : alternatingGroup (Fin n)) : Perm (Fin n)) h} :=
      card_class_replicate_gt n r (by omega) hr2 h3r hct
    have hle : Fintype.card {h : Perm (Fin n) // IsConj ((φ c : alternatingGroup (Fin n)) : Perm (Fin n)) h} ≤
        2 * (Finset.univ.filter fun g : Perm (Fin n) => g.IsThreeCycle).card := by
      exact (card_class_A_ge_half (by omega) (φ c)).trans (Nat.mul_le_mul_left 2 hA)
    exact (not_lt_of_ge hle) hgt
  -- r = 1: the cycle type is {3}, i.e. φ(c) is a 3-cycle
  rw [hr'] at hct
  simpa [IsThreeCycle] using hct

/-! ### Milestone 4: 3-cycle combinatorics -/

/-- The product of two 3-cycles `(a b c)(a b d)` sharing the pair `{a, b}` in the
same direction is the double transposition `(a c)(b d)`. -/
private theorem P_same {α : Type*} [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d) :
    (Equiv.swap a b * Equiv.swap b c) * (Equiv.swap a b * Equiv.swap b d) =
      Equiv.swap a c * Equiv.swap b d := by
  ext x
  by_cases hx : x ∈ ({a, b, c, d} : Finset α)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp only [Equiv.Perm.mul_apply] <;> grind
  · have hxa : x ≠ a := by intro h; exact hx (by simp [h])
    have hxb : x ≠ b := by intro h; exact hx (by simp [h])
    have hxc : x ≠ c := by intro h; exact hx (by simp [h])
    have hxd : x ≠ d := by intro h; exact hx (by simp [h])
    simp only [Equiv.Perm.mul_apply]
    grind

/-- Rotating a 3-cycle: `(a b c) = (b c a)` as swap products. -/
private theorem threeCycle_rotate {α : Type*} [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Equiv.swap a b * Equiv.swap b c = Equiv.swap b c * Equiv.swap c a := by
  ext x
  by_cases hx : x ∈ ({a, b, c} : Finset α)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp only [Equiv.Perm.mul_apply] <;> grind
  · have hxa : x ≠ a := by intro h; exact hx (by simp [h])
    have hxb : x ≠ b := by intro h; exact hx (by simp [h])
    have hxc : x ≠ c := by intro h; exact hx (by simp [h])
    simp only [Equiv.Perm.mul_apply]
    grind

/-- For a 3-cycle `g`, the two points of the support other than `a` are `g a` and
`g (g a)`. -/
private theorem threeCycle_support_eq {α : Type*} [Fintype α] [DecidableEq α]
    {g : Equiv.Perm α} (hg : g.IsThreeCycle) {a : α} (ha : a ∈ g.support) :
    g.support = ({a, g a, g (g a)} : Finset α) :=
  hg.support_eq_iff_mem_support.mpr ha

/-- Direction: for `a ∈ supp g`, `b ∈ supp g`, `a ≠ b`: `g a = b` or `g b = a`. -/
private theorem threeCycle_direction {α : Type*} [Fintype α] [DecidableEq α]
    {g : Equiv.Perm α} (hg : g.IsThreeCycle) {a b : α}
    (ha : a ∈ g.support) (hb : b ∈ g.support) (hab : a ≠ b) : g a = b ∨ g b = a := by
  have hsupp := hg.support_eq_iff_mem_support.mpr ha
  have h3 : g ^ 3 = 1 := by simpa [hg.orderOf] using pow_orderOf_eq_one g
  have h3a : (g ^ 3) a = a := by rw [h3]; simp
  rw [hsupp] at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with hba | hbga | hbgga
  · exact (hab hba.symm).elim
  · exact Or.inl hbga.symm
  · right
    rw [hbgga]
    simpa [pow_succ, pow_two] using h3a

/-- Two 3-cycles with the same support and agreeing at a point of the support are
equal. -/
private theorem threeCycle_eq_of_agree {α : Type*} [Fintype α] [DecidableEq α]
    {g g' : Equiv.Perm α} (hg : g.IsThreeCycle) (hg' : g'.IsThreeCycle)
    (hss : g.support = g'.support) {a : α} (ha : a ∈ g.support) (hga : g' a = g a) : g = g' := by
  have ha' : a ∈ g'.support := by rwa [← hss]
  have hsupp := hg.support_eq_iff_mem_support.mpr ha
  have hnd' := hg'.nodup_iff_mem_support.mpr ha'
  have hg'ga : g' (g a) = g (g a) := by
    have h1 : g' (g a) ∈ g'.support := (Equiv.Perm.apply_mem_support).2
      (by simpa [hga] using (Equiv.Perm.apply_mem_support).2 ha')
    have h2 : g' (g a) ∉ ({a, g a} : Finset α) := by
      rw [hga] at hnd'
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      have hnd'' : (¬a = g a ∧ ¬a = g' (g a)) ∧ ¬g a = g' (g a) := by simpa using hnd'
      exact ⟨fun h => hnd''.1.2 h.symm, fun h => hnd''.2 h.symm⟩
    rw [← hss] at h1
    rw [hsupp] at h1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with h1a | h1b | h1c
    · exact (h2 (by simp [h1a])).elim
    · exact (h2 (by simp [h1b])).elim
    · exact h1c
  have hg'form : g' = Equiv.swap a (g a) * Equiv.swap (g a) (g (g a)) := by
    calc
      g' = Equiv.swap a (g' a) * Equiv.swap (g' a) (g' (g' a)) :=
        hg'.eq_swap_mul_swap_iff_mem_support.mpr ha'
      _ = Equiv.swap a (g a) * Equiv.swap (g a) (g (g a)) := by
        rw [hga, hg'ga]
  have hgform : g = Equiv.swap a (g a) * Equiv.swap (g a) (g (g a)) := by
    exact hg.eq_swap_mul_swap_iff_mem_support.mpr ha
  exact hgform.trans hg'form.symm

/-- A 3-cycle satisfies `g⁻¹ = g * g`. -/
private theorem threeCycle_inv_eq_sq {α : Type*} [Fintype α] [DecidableEq α]
    {g : Equiv.Perm α} (hg : g.IsThreeCycle) : g⁻¹ = g * g := by
  apply inv_eq_of_mul_eq_one_left (a := g * g) (b := g)
  have h3 : g ^ 3 = 1 := by simpa [hg.orderOf] using pow_orderOf_eq_one g
  simpa [pow_succ, pow_two] using h3

/-- Two 3-cycles with the same support are equal or inverse. -/
private theorem threeCycle_eq_or_inv_of_support_eq {α : Type*} [Fintype α] [DecidableEq α]
    {g g' : Equiv.Perm α} (hg : g.IsThreeCycle) (hg' : g'.IsThreeCycle)
    (hss : g.support = g'.support) : g = g' ∨ g = g'⁻¹ := by
  have hne : (g.support : Finset α).Nonempty := by
    rw [← Finset.card_pos, hg.card_support]
    norm_num
  obtain ⟨a, ha⟩ := hne
  have ha' : a ∈ g'.support := by rwa [← hss]
  by_cases h : g' a = g a
  · left
    exact threeCycle_eq_of_agree hg hg' hss ha h
  · right
    have hg'a : g' a = g (g a) := by
      have h1 : g' a ∈ g'.support := (Equiv.Perm.apply_mem_support).2 ha'
      have h2 : g' a ≠ a := by simpa [Equiv.Perm.mem_support] using ha'
      rw [← hss] at h1
      have hsupp := hg.support_eq_iff_mem_support.mpr ha
      rw [hsupp] at h1
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      rcases h1 with h1a | h1b | h1c
      · exact (h2 h1a).elim
      · exact (h h1b).elim
      · exact h1c
    have hg'a2 : g⁻¹ a = g (g a) := by
      rw [threeCycle_inv_eq_sq hg]
      rfl
    have hg' : g' = g⁻¹ := by
      exact threeCycle_eq_of_agree hg' hg.inv
        (by rw [Equiv.Perm.support_inv, hss])
        (by simpa [Equiv.Perm.support_inv, hss] using ha') (hg'a2.trans hg'a.symm)
    rw [hg']
    simp

/-- Two 3-cycles `x, y` with `orderOf (x * y) = 2` share exactly two points, in the
same direction: `x = (a b c)` and `y = (a b d)`. -/
private theorem threeCycle_mul_order2 {α : Type*} [Fintype α] [DecidableEq α]
    {x y : Equiv.Perm α} (hx : x.IsThreeCycle) (hy : y.IsThreeCycle)
    (hxy : orderOf (x * y) = 2) :
    ∃ a b c d, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ≠ d ∧ b ≠ d ∧ c ≠ d ∧
      x = Equiv.swap a b * Equiv.swap b c ∧
      y = Equiv.swap a b * Equiv.swap b d := by
  have hsq : (x * y) * (x * y) = 1 := by simpa [hxy, pow_two] using pow_orderOf_eq_one (x * y)
  have hne_supp : x.support ≠ y.support := by
    intro hss
    rcases threeCycle_eq_or_inv_of_support_eq hx hy hss with hxeq | hxinv
    · have h3 : orderOf (x * y) = 3 := by
        rw [hxeq, ← pow_two, orderOf_pow, ← hxeq, hx.orderOf]
        norm_num
      omega
    · have h1 : orderOf (x * y) = 1 := by
        rw [hxinv]
        simp
      omega
  have hdiff : ∃ a, a ∈ x.support ∧ a ∉ y.support := by
    by_contra h
    have hsub : x.support ⊆ y.support := by
      intro z hz
      by_contra hz'
      exact h ⟨z, hz, hz'⟩
    exact hne_supp
      (Finset.eq_of_subset_of_card_le hsub (by rw [hx.card_support, hy.card_support]))
  rcases hdiff with ⟨a, hax, hay⟩
  have hnd := hx.nodup_iff_mem_support.mpr hax
  have hnd' : (¬a = x a ∧ ¬a = x (x a)) ∧ ¬x a = x (x a) := by simpa using hnd
  set b := x a with hb
  set c := x (x a) with hc
  have hab : a ≠ b := by simpa [hb] using hnd'.1.1
  have hac : a ≠ c := by simpa [hc] using hnd'.1.2
  have hbc : b ≠ c := by simpa [hb, hc] using hnd'.2
  have hxform : x = Equiv.swap a b * Equiv.swap b c := by
    have hf : x = Equiv.swap a (x a) * Equiv.swap (x a) (x (x a)) :=
      hx.eq_swap_mul_swap_iff_mem_support.mpr hax
    simpa [hb, hc] using hf
  have hxsupp : x.support = ({a, b, c} : Finset α) := by
    have hf : x.support = ({a, x a, x (x a)} : Finset α) := hx.support_eq_iff_mem_support.mpr hax
    simpa [hb, hc] using hf
  have hya : y a = a := by
    by_contra h
    exact hay ((Equiv.Perm.mem_support).2 h)
  by_cases hbT : b ∈ y.support
  · by_cases hcT : c ∈ y.support
    · -- both b, c in T_y
      have hdir := threeCycle_direction hy hbT hcT hbc
      rcases hdir with hybc | hycb
      · -- same direction: y b = c -- good case
        set d := y (y b) with hd
        have hyd : y = Equiv.swap b c * Equiv.swap c d := by
          have hf : y = Equiv.swap b (y b) * Equiv.swap (y b) (y (y b)) :=
            hy.eq_swap_mul_swap_iff_mem_support.mpr hbT
          calc
            y = Equiv.swap b (y b) * Equiv.swap (y b) (y (y b)) := hf
            _ = Equiv.swap b c * Equiv.swap c d := by simp [hybc, hd]
        have hndy := hy.nodup_iff_mem_support.mpr hbT
        have hndy' : (¬b = y b ∧ ¬b = y (y b)) ∧ ¬y b = y (y b) := by simpa using hndy
        have hdb : d ≠ b := by
          intro h
          exact hndy'.1.2 h.symm
        have hdc : d ≠ c := by
          intro h
          exact hndy'.2 (hybc.trans h.symm)
        have hda : d ≠ a := by
          intro hda
          have hTy : y.support = ({b, c, d} : Finset α) := by
            have hf : y.support = ({b, y b, y (y b)} : Finset α) :=
              hy.support_eq_iff_mem_support.mpr hbT
            simpa [hybc, hd] using hf
          have hTy' : y.support = ({b, c, a} : Finset α) := by simpa [hda] using hTy
          exact hne_supp (by rw [hxsupp, hTy']; ext i; simp only [Finset.mem_insert,
            Finset.mem_singleton]; tauto)
        have hxrot : x = Equiv.swap b c * Equiv.swap c a := by
          have hr : Equiv.swap a b * Equiv.swap b c = Equiv.swap b c * Equiv.swap c a :=
            threeCycle_rotate hab hac hbc
          exact hxform.trans hr
        refine ⟨b, c, a, d, hbc, hab.symm, hac.symm, hdb.symm, hdc.symm, hda.symm, hxrot, hyd⟩
      · -- opposite direction: y c = b -- contradiction
        set d := y b with hd
        have hyd : y = Equiv.swap c b * Equiv.swap b d := by
          have hf : y = Equiv.swap c (y c) * Equiv.swap (y c) (y (y c)) :=
            hy.eq_swap_mul_swap_iff_mem_support.mpr hcT
          calc
            y = Equiv.swap c (y c) * Equiv.swap (y c) (y (y c)) := hf
            _ = Equiv.swap c b * Equiv.swap b d := by simp [hycb, hd]
        have hda : d ≠ a := by
          intro hda
          exact hay (by simpa [← hd, hda] using (Equiv.Perm.apply_mem_support).2 hbT)
        have hdb : d ≠ b := by
          intro h
          exact (Equiv.Perm.mem_support.mp hbT) (by simpa [hd] using h)
        have hdc : d ≠ c := by
          intro hdc
          have hndy := hy.nodup_iff_mem_support.mpr hcT
          have hndy' : (¬c = y c ∧ ¬c = y (y c)) ∧ ¬y c = y (y c) := by simpa using hndy
          apply hndy'.1.2
          calc
            c = d := hdc.symm
            _ = y b := hd
            _ = y (y c) := (congrArg y hycb).symm
        have hdTx : d ∉ x.support := by
          rw [hxsupp]
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hda, hdb, hdc⟩
        have hxd : x d = d := by
          by_contra h
          exact hdTx ((Equiv.Perm.mem_support).2 h)
        have h1 : ((x * y) * (x * y)) a = d := by
          calc
            ((x * y) * (x * y)) a = x (y (x (y a))) := by simp [Equiv.Perm.mul_apply]
            _ = x (y (x a)) := by rw [hya]
            _ = x (y b) := by rw [← hb]
            _ = x d := by rw [← hd]
            _ = d := hxd
        have h2 : ((x * y) * (x * y)) a = a := by rw [hsq]; simp
        exact (hda (h1.symm.trans h2)).elim
    · -- b in T_y, c not -- contradiction
      set d := y b with hd
      have hda : d ≠ a := by
        intro hda
        exact hay (by simpa [← hd, hda] using (Equiv.Perm.apply_mem_support).2 hbT)
      have hdb : d ≠ b := by
        intro h
        exact (Equiv.Perm.mem_support.mp hbT) (by simpa [hd] using h)
      have hdc : d ≠ c := by
        intro hdc
        exact hcT (by simpa [← hd, hdc] using (Equiv.Perm.apply_mem_support).2 hbT)
      have hdTx : d ∉ x.support := by
        rw [hxsupp]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hda, hdb, hdc⟩
      have hxd : x d = d := by
        by_contra h
        exact hdTx ((Equiv.Perm.mem_support).2 h)
      have h1 : ((x * y) * (x * y)) a = d := by
        calc
          ((x * y) * (x * y)) a = x (y (x (y a))) := by simp [Equiv.Perm.mul_apply]
          _ = x (y (x a)) := by rw [hya]
          _ = x (y b) := by rw [← hb]
          _ = x d := by rw [← hd]
          _ = d := hxd
      have h2 : ((x * y) * (x * y)) a = a := by rw [hsq]; simp
      exact (hda (h1.symm.trans h2)).elim
  · by_cases hcT : c ∈ y.support
    · -- c in T_y, b not -- contradiction
      have hyb : y b = b := by
        by_contra h
        exact hbT ((Equiv.Perm.mem_support).2 h)
      have hxb : x b = c := by
        rw [hxform]
        simp only [Equiv.Perm.mul_apply]
        grind
      have h1 : ((x * y) * (x * y)) a = c := by
        calc
          ((x * y) * (x * y)) a = x (y (x (y a))) := by simp [Equiv.Perm.mul_apply]
          _ = x (y (x a)) := by rw [hya]
          _ = x (y b) := by rw [← hb]
          _ = x b := by rw [hyb]
          _ = c := hxb
      have h2 : ((x * y) * (x * y)) a = a := by rw [hsq]; simp
      exact (hac.symm (h1.symm.trans h2)).elim
    · -- neither -- contradiction
      have hyb : y b = b := by
        by_contra h
        exact hbT ((Equiv.Perm.mem_support).2 h)
      have hxb : x b = c := by
        rw [hxform]
        simp only [Equiv.Perm.mul_apply]
        grind
      have h1 : ((x * y) * (x * y)) a = c := by
        calc
          ((x * y) * (x * y)) a = x (y (x (y a))) := by simp [Equiv.Perm.mul_apply]
          _ = x (y (x a)) := by rw [hya]
          _ = x (y b) := by rw [← hb]
          _ = x b := by rw [hyb]
          _ = c := hxb
      have h2 : ((x * y) * (x * y)) a = a := by rw [hsq]; simp
      exact (hac.symm (h1.symm.trans h2)).elim

/-- A 3-cycle written as `swap p q * swap q r` has exactly the three rotation
representations `(p, q, r)`, `(q, r, p)`, `(r, p, q)`. -/
private theorem threeCycle_repr {α : Type*} [Fintype α] [DecidableEq α] {p q r a b c : α}
    (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (h : Equiv.swap p q * Equiv.swap q r = Equiv.swap a b * Equiv.swap b c) :
    a = p ∧ b = q ∧ c = r ∨ a = q ∧ b = r ∧ c = p ∨ a = r ∧ b = p ∧ c = q := by
  classical
  have hmem : a ∈ (Equiv.swap p q * Equiv.swap q r).support := by
    rw [h]
    have h' : a ∈ (Equiv.swap b a * Equiv.swap b c).support := by
      rw [support_swap_mul_swap_same (i := b) (j := a) (k := c) hab.symm hbc hca.symm]
      simp
    simpa [swap_comm] using h'
  have hpqr : a = p ∨ a = q ∨ a = r := by
    have h'' : a ∈ ({q, p, r} : Finset α) := by
      have hs : (Equiv.swap p q * Equiv.swap q r).support = ({q, p, r} : Finset α) := by
        rw [swap_comm]
        exact support_swap_mul_swap_same (i := q) (j := p) (k := r) hpq.symm hqr hrp.symm
      rwa [hs] at hmem
    have h''' : a = q ∨ a = p ∨ a = r := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using h''
    tauto
  rcases hpqr with hpa | hqa | hra
  · have hpb : p ≠ b := by simpa [hpa] using hab
    have hpc : p ≠ c := by simpa [hpa] using hca.symm
    have hqr_p : Equiv.swap q r p = p := Equiv.swap_apply_of_ne_of_ne hpq hrp.symm
    have hbc_p : Equiv.swap b c p = p := Equiv.swap_apply_of_ne_of_ne hpb hpc
    have hpq_r : Equiv.swap p q r = r := Equiv.swap_apply_of_ne_of_ne hrp hqr.symm
    have hpb_c : Equiv.swap p b c = c := Equiv.swap_apply_of_ne_of_ne hpc.symm hbc.symm
    have hb : b = q := by
      have h₁ := congrArg (fun t : Equiv.Perm α => t p) h
      have h₂ : q = b := by simpa [hpa, mul_apply, hqr_p, hbc_p, swap_apply_left] using h₁
      exact h₂.symm
    have hc : c = r := by
      have h₁ := congrArg (fun t : Equiv.Perm α => t (t p)) h
      have h₂ : r = c := by
        simpa [hpa, mul_apply, hqr_p, hbc_p, hpq_r, hpb_c, swap_apply_left, swap_apply_right]
          using h₁
      exact h₂.symm
    exact Or.inl ⟨hpa, hb, hc⟩
  · have hqb' : q ≠ b := by simpa [hqa] using hab
    have hqc : q ≠ c := by
      have h₂ : c ≠ q := by simpa [hqa] using hca
      exact h₂.symm
    have hqr_q : Equiv.swap q r q = r := swap_apply_left q r
    have hpq_r : Equiv.swap p q r = r := Equiv.swap_apply_of_ne_of_ne hrp hqr.symm
    have hbc_q : Equiv.swap b c q = q := Equiv.swap_apply_of_ne_of_ne hqb' hqc
    have hqb_c : Equiv.swap q b c = c := Equiv.swap_apply_of_ne_of_ne hqc.symm hbc.symm
    have hb : b = r := by
      have h₁ := congrArg (fun t : Equiv.Perm α => t q) h
      have h₂ : r = b := by
        simpa [hqa, mul_apply, hqr_q, hpq_r, hbc_q, swap_apply_left] using h₁
      exact h₂.symm
    have hc : c = p := by
      have h₁ := congrArg (fun t : Equiv.Perm α => t (t q)) h
      have h₂ : p = c := by
        simpa [hqa, mul_apply, hqr_q, hpq_r, hbc_q, hqb_c, swap_apply_left, swap_apply_right]
          using h₁
      exact h₂.symm
    exact Or.inr (Or.inl ⟨hqa, hb, hc⟩)
  · have hrb : r ≠ b := by simpa [hra] using hab
    have hrc' : r ≠ c := by
      have h₂ : c ≠ r := by simpa [hra] using hca
      exact h₂.symm
    have hqr_r : Equiv.swap q r r = q := swap_apply_right q r
    have hbc_r : Equiv.swap b c r = r := Equiv.swap_apply_of_ne_of_ne hrb hrc'
    have hqr_p' : Equiv.swap q r p = p := Equiv.swap_apply_of_ne_of_ne hpq hrp.symm
    have hrb_c : Equiv.swap r b c = c := Equiv.swap_apply_of_ne_of_ne hrc'.symm hbc.symm
    have hb : b = p := by
      have h₁ := congrArg (fun t : Equiv.Perm α => t r) h
      have h₂ : p = b := by
        simpa [hra, mul_apply, hqr_r, hbc_r, swap_apply_left, swap_apply_right] using h₁
      exact h₂.symm
    have hc : c = q := by
      have h₁ := congrArg (fun t : Equiv.Perm α => t (t r)) h
      have h₂ : q = c := by
        simpa [hra, mul_apply, hqr_p', hbc_r, hrb_c, swap_apply_left, swap_apply_right] using h₁
      exact h₂.symm
    exact Or.inr (Or.inr ⟨hra, hb, hc⟩)

/-- An oriented pair of `(a b d)` never coincides with an oriented pair of `(p q t)`
when `(p, q) = (b, c)` or `(c, a)` and `t` avoids `{a, b}`. -/
private theorem no_common_oriented_pair {α : Type*} [DecidableEq α] {a b c d p q t u v : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hta : t ≠ a) (htb : t ≠ b)
    (hpq : (p, q) = (b, c) ∨ (p, q) = (c, a))
    (hu : (u, v) = (a, b) ∨ (u, v) = (b, d) ∨ (u, v) = (d, a))
    (hv : (u, v) = (p, q) ∨ (u, v) = (q, t) ∨ (u, v) = (t, p)) : False := by
  have hpair : ((u, v) : α × α) ∈ ({(a, b), (b, d), (d, a)} : Finset (α × α)) := by
    rcases hu with hu | hu | hu <;> rcases (by simpa [Prod.ext_iff] using hu) with ⟨rfl, rfl⟩ <;> simp
  rcases hpq with hpq | hpq
  · -- (p, q) = (b, c)
    have hp' : p = b := (by simpa [Prod.ext_iff] using hpq : p = b ∧ q = c).1
    have hq' : q = c := (by simpa [Prod.ext_iff] using hpq : p = b ∧ q = c).2
    rcases hv with hv | hv | hv
    · rw [hv.trans hpq] at hpair
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at hpair
      rcases hpair with hpair | hpair | hpair
      all_goals rcases hpair with ⟨hp, hq⟩
      all_goals first | exact hab hp.symm | exact hcd hq | exact hbd hp
    · rw [hq'] at hv
      rw [hv] at hpair
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at hpair
      rcases hpair with hpair | hpair | hpair
      all_goals rcases hpair with ⟨hp, hq⟩
      all_goals first | exact hac hp.symm | exact hbc hp.symm | exact hcd hp
    · rw [hp'] at hv
      rw [hv] at hpair
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at hpair
      rcases hpair with hpair | hpair | hpair
      all_goals rcases hpair with ⟨hp, hq⟩
      all_goals first | exact hta hp | exact htb hp | exact hab hq.symm
  · -- (p, q) = (c, a)
    have hp' : p = c := (by simpa [Prod.ext_iff] using hpq : p = c ∧ q = a).1
    have hq' : q = a := (by simpa [Prod.ext_iff] using hpq : p = c ∧ q = a).2
    rcases hv with hv | hv | hv
    · rw [hv.trans hpq] at hpair
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at hpair
      rcases hpair with hpair | hpair | hpair
      all_goals rcases hpair with ⟨hp, hq⟩
      all_goals first | exact hac hp.symm | exact hbc hp.symm | exact hcd hp
    · rw [hq'] at hv
      rw [hv] at hpair
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at hpair
      rcases hpair with hpair | hpair | hpair
      all_goals rcases hpair with ⟨hp, hq⟩
      all_goals first | exact htb hq | exact hab hp | exact had hp
    · rw [hp'] at hv
      rw [hv] at hpair
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at hpair
      rcases hpair with hpair | hpair | hpair
      all_goals rcases hpair with ⟨hp, hq⟩
      all_goals first | exact hta hp | exact htb hp | exact hac hq.symm

/-- If `x = (a b c)` and `y = (a b d)` are 3-cycles and `z` is a 3-cycle with
`orderOf (x * z) = orderOf (y * z) = 2`, then `z = (a b e)` for some `e` outside
`{a, b, c, d}`. -/
private theorem threeCycle_star_anchor {α : Type*} [Fintype α] [DecidableEq α]
    {x y z : Equiv.Perm α} {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hx : x.IsThreeCycle) (hy : y.IsThreeCycle) (hz : z.IsThreeCycle)
    (hxform : x = Equiv.swap a b * Equiv.swap b c)
    (hyform : y = Equiv.swap a b * Equiv.swap b d)
    (hxz : orderOf (x * z) = 2) (hyz : orderOf (y * z) = 2) :
    ∃ e : α, a ≠ e ∧ b ≠ e ∧ c ≠ e ∧ d ≠ e ∧ z = Equiv.swap a b * Equiv.swap b e := by
  classical
  obtain ⟨a', b', c', d', ha'b', ha'c', hb'c', ha'd', hb'd', hc'd', hxform', hzform'⟩ :=
    threeCycle_mul_order2 hx hz hxz
  have hrot : a' = a ∧ b' = b ∧ c' = c ∨ a' = b ∧ b' = c ∧ c' = a ∨ a' = c ∧ b' = a ∧ c' = b :=
    threeCycle_repr (p := a) (q := b) (r := c) (hpq := hab) (hqr := hbc) (hrp := hac.symm)
      (hab := ha'b') (hbc := hb'c') (hca := ha'c'.symm) (h := hxform.symm.trans hxform')
  rcases hrot with hrot | hrot | hrot
  · -- z shares the pair {a, b} in the same direction: z = (a b d')
    rcases hrot with ⟨ha', hb', hc'⟩
    simp_rw [ha', hb', hc'] at hzform' ha'd' hb'd' hc'd'
    have hdd' : d ≠ d' := by
      intro hdd'
      have hzy : z = y := by
        calc
          z = Equiv.swap a b * Equiv.swap b d' := hzform'
          _ = Equiv.swap a b * Equiv.swap b d := by rw [hdd']
          _ = y := hyform.symm
      have hord : orderOf (y * z) = 3 := by
        rw [hzy]
        rw [← pow_two, orderOf_pow, hy.orderOf]
        norm_num
      omega
    exact ⟨d', ha'd', hb'd', hc'd', hdd', hzform'⟩
  · -- z = (b c d'): no oriented pair of z is an oriented pair of y
    rcases hrot with ⟨ha', hb', hc'⟩
    simp_rw [ha', hb', hc'] at hzform' ha'd' hb'd' hc'd'
    obtain ⟨a₁, b₁, c₁, d₁, ha₁b₁, ha₁c₁, hb₁c₁, ha₁d₁, hb₁d₁, hc₁d₁, hyform₁, hzform₁⟩ :=
      threeCycle_mul_order2 hy hz hyz
    have hry : a₁ = a ∧ b₁ = b ∧ c₁ = d ∨ a₁ = b ∧ b₁ = d ∧ c₁ = a ∨
        a₁ = d ∧ b₁ = a ∧ c₁ = b :=
      threeCycle_repr (p := a) (q := b) (r := d) (hpq := hab) (hqr := hbd) (hrp := had.symm)
        (hab := ha₁b₁) (hbc := hb₁c₁) (hca := ha₁c₁.symm) (h := hyform.symm.trans hyform₁)
    have hrz : a₁ = b ∧ b₁ = c ∧ d₁ = d' ∨ a₁ = c ∧ b₁ = d' ∧ d₁ = b ∨
        a₁ = d' ∧ b₁ = b ∧ d₁ = c :=
      threeCycle_repr (p := b) (q := c) (r := d') (hpq := hbc) (hqr := hb'd') (hrp := ha'd'.symm)
        (hab := ha₁b₁) (hbc := hb₁d₁) (hca := ha₁d₁.symm) (h := hzform'.symm.trans hzform₁)
    have hu : (a₁, b₁) = (a, b) ∨ (a₁, b₁) = (b, d) ∨ (a₁, b₁) = (d, a) := by
      rcases hry with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp
    have hv : (a₁, b₁) = (b, c) ∨ (a₁, b₁) = (c, d') ∨ (a₁, b₁) = (d', b) := by
      rcases hrz with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp
    exfalso
    exact no_common_oriented_pair (p := b) (q := c) (t := d') (u := a₁) (v := b₁) hab hac hbc
      had hbd hcd hc'd'.symm ha'd'.symm (Or.inl rfl) hu hv
  · -- z = (c a d'): no oriented pair of z is an oriented pair of y
    rcases hrot with ⟨ha', hb', hc'⟩
    simp_rw [ha', hb', hc'] at hzform' ha'd' hb'd' hc'd'
    obtain ⟨a₁, b₁, c₁, d₁, ha₁b₁, ha₁c₁, hb₁c₁, ha₁d₁, hb₁d₁, hc₁d₁, hyform₁, hzform₁⟩ :=
      threeCycle_mul_order2 hy hz hyz
    have hry : a₁ = a ∧ b₁ = b ∧ c₁ = d ∨ a₁ = b ∧ b₁ = d ∧ c₁ = a ∨
        a₁ = d ∧ b₁ = a ∧ c₁ = b :=
      threeCycle_repr (p := a) (q := b) (r := d) (hpq := hab) (hqr := hbd) (hrp := had.symm)
        (hab := ha₁b₁) (hbc := hb₁c₁) (hca := ha₁c₁.symm) (h := hyform.symm.trans hyform₁)
    have hrz : a₁ = c ∧ b₁ = a ∧ d₁ = d' ∨ a₁ = a ∧ b₁ = d' ∧ d₁ = c ∨
        a₁ = d' ∧ b₁ = c ∧ d₁ = a :=
      threeCycle_repr (p := c) (q := a) (r := d') (hpq := hac.symm) (hqr := hb'd') (hrp := ha'd'.symm)
        (hab := ha₁b₁) (hbc := hb₁d₁) (hca := ha₁d₁.symm) (h := hzform'.symm.trans hzform₁)
    have hu : (a₁, b₁) = (a, b) ∨ (a₁, b₁) = (b, d) ∨ (a₁, b₁) = (d, a) := by
      rcases hry with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp
    have hv : (a₁, b₁) = (c, a) ∨ (a₁, b₁) = (a, d') ∨ (a₁, b₁) = (d', c) := by
      rcases hrz with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp
    exfalso
    exact no_common_oriented_pair (p := c) (q := a) (t := d') (u := a₁) (v := b₁) hab hac hbc
      had hbd hcd hb'd'.symm hc'd'.symm (Or.inr rfl) hu hv

/-- The points of `Fin n` different from `0` and `1` (needed since `(0 : Fin n)`
and `(1 : Fin n)` are not numerals available for a variable `n`). -/
private abbrev points_off (n : ℕ) [NeZero n] (_hn : 5 ≤ n) :=
  {i : Fin n // i ≠ (0 : Fin n) ∧ i ≠ (1 : Fin n)}

/-- A family of 3-cycles indexed by the points other than `0` and `1`, pairwise with
products of order `2`, all have the form `(a b (f i))` for a common pair `{a, b}` and
an injective third-point function `f`. -/
private theorem threeCycle_family (n : ℕ) [NeZero n] (hn : 5 ≤ n)
    {h : points_off n hn → Perm (Fin n)}
    (h3c : ∀ i, (h i).IsThreeCycle)
    (hord : ∀ i j, i ≠ j → orderOf (h i * h j) = 2) (hinj : Function.Injective h) :
    ∃ a b : Fin n, a ≠ b ∧ ∃ f : points_off n hn → Fin n,
      (∀ i, a ≠ f i ∧ b ≠ f i) ∧ Function.Injective f ∧
      ∀ i, h i = Equiv.swap a b * Equiv.swap b (f i) := by
  classical
  have h20 : (⟨2, by omega⟩ : Fin n) ≠ (0 : Fin n) := by
    intro h; have hv := congrArg Fin.val h; simp at hv
  have h21 : (⟨2, by omega⟩ : Fin n) ≠ (1 : Fin n) := by
    intro h; have hv := congrArg Fin.val h; simp at hv; rw [Nat.mod_eq_of_lt (by omega)] at hv; norm_num at hv
  have h30 : (⟨3, by omega⟩ : Fin n) ≠ (0 : Fin n) := by
    intro h; have hv := congrArg Fin.val h; simp at hv
  have h31 : (⟨3, by omega⟩ : Fin n) ≠ (1 : Fin n) := by
    intro h; have hv := congrArg Fin.val h; simp at hv; rw [Nat.mod_eq_of_lt (by omega)] at hv; norm_num at hv
  let i2 : points_off n hn := ⟨⟨2, by omega⟩, h20, h21⟩
  let i3 : points_off n hn := ⟨⟨3, by omega⟩, h30, h31⟩
  have hi23 : i2 ≠ i3 := by
    intro h
    have hv := congrArg (fun t : points_off n hn => t.1) h
    have h23 : (⟨2, by omega⟩ : Fin n) ≠ (⟨3, by omega⟩ : Fin n) := by
      intro h23
      have hv := congrArg Fin.val h23
      simp at hv
    exact h23 hv
  obtain ⟨a, b, c, d, hab, hac, hbc, had, hbd, hcd, h2form, h3form⟩ :=
    threeCycle_mul_order2 (h3c i2) (h3c i3) (hord i2 i3 hi23)
  have hstar : ∀ i : points_off n hn, i ≠ i2 → i ≠ i3 →
      ∃ e : Fin n, a ≠ e ∧ b ≠ e ∧ c ≠ e ∧ d ≠ e ∧ h i = Equiv.swap a b * Equiv.swap b e := by
    intro i hi2 hi3
    exact threeCycle_star_anchor (hab := hab) (hac := hac) (hbc := hbc) (had := had)
      (hbd := hbd) (hcd := hcd) (hx := h3c i2) (hy := h3c i3) (hz := h3c i)
      (hxform := h2form) (hyform := h3form)
      (hxz := hord i2 i (Ne.symm hi2)) (hyz := hord i3 i (Ne.symm hi3))
  have hthird : ∀ i : points_off n hn,
      ∃ e : Fin n, a ≠ e ∧ b ≠ e ∧ h i = Equiv.swap a b * Equiv.swap b e ∧
        ∀ e', h i = Equiv.swap a b * Equiv.swap b e' → e = e' := by
    intro i
    by_cases hi2 : i = i2
    · subst hi2
      exact ⟨c, hac, hbc, h2form, by
        intro e' he'
        have hsw : Equiv.swap b c = Equiv.swap b e' :=
          mul_left_cancel (h2form.symm.trans he')
        have hb := congrArg (fun t : Perm (Fin n) => t b) hsw
        simpa using hb⟩
    · by_cases hi3 : i = i3
      · subst hi3
        exact ⟨d, had, hbd, h3form, by
          intro e' he'
          have hsw : Equiv.swap b d = Equiv.swap b e' :=
            mul_left_cancel (h3form.symm.trans he')
          have hb := congrArg (fun t : Perm (Fin n) => t b) hsw
          simpa using hb⟩
      · obtain ⟨e, hae, hbe, _hce, _hde, hie⟩ := hstar i hi2 hi3
        refine ⟨e, hae, hbe, hie, ?_⟩
        intro e' he'
        have hsw : Equiv.swap b e = Equiv.swap b e' := mul_left_cancel (hie.symm.trans he')
        have hb := congrArg (fun t : Perm (Fin n) => t b) hsw
        simpa using hb
  refine ⟨a, b, hab, ?_⟩
  let f : points_off n hn → Fin n := fun i => Classical.choose (hthird i)
  refine ⟨f, ?hfne, ?hfinj, ?hfam⟩
  · intro i
    exact ⟨(Classical.choose_spec (hthird i)).1, (Classical.choose_spec (hthird i)).2.1⟩
  · intro i j hij
    have hh : h i = h j := by
      calc
        h i = Equiv.swap a b * Equiv.swap b (f i) := (Classical.choose_spec (hthird i)).2.2.1
        _ = Equiv.swap a b * Equiv.swap b (f j) := by rw [hij]
        _ = h j := (Classical.choose_spec (hthird j)).2.2.1.symm
    exact hinj hh
  · intro i
    exact (Classical.choose_spec (hthird i)).2.2.1

/-! ### Milestone 4: the generators `(0 1 i)` and the induced permutation -/

/-- The generator `(0 1 i) = (swap 0 1) (1 i)` of `Aₙ`. -/
private def genPerm (n : ℕ) [NeZero n] (i : Fin n) : Equiv.Perm (Fin n) :=
  Equiv.swap (0 : Fin n) 1 * Equiv.swap 1 i

/-- In a type `Fin n` with `2 ≤ n`, the points `0` and `1` are distinct. -/
private theorem fin_one_ne_zero {n : ℕ} [NeZero n] (hn : 2 ≤ n) : (1 : Fin n) ≠ 0 := by
  intro h
  have hv : (1 : Fin n).val = (0 : Fin n).val := congrArg Fin.val h
  simp at hv
  have hmod : 1 % n = 1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  omega

private theorem genPerm_isThreeCycle {n : ℕ} [NeZero n] (hn : 2 ≤ n) {i : Fin n}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) : (genPerm n i).IsThreeCycle := by
  have h10 : (1 : Fin n) ≠ 0 := fin_one_ne_zero hn
  have h01 : (0 : Fin n) ≠ 1 := h10.symm
  have h1i : (1 : Fin n) ≠ i := hi1.symm
  have h0i : (0 : Fin n) ≠ i := hi0.symm
  simpa [genPerm, swap_comm] using
    (Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := (1 : Fin n)) (b := (0 : Fin n))
      (c := i) h10 h1i h0i)

private theorem genPerm_mem_alternatingGroup {n : ℕ} [NeZero n] (hn : 2 ≤ n) {i : Fin n}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) : genPerm n i ∈ alternatingGroup (Fin n) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  exact (genPerm_isThreeCycle hn hi0 hi1).sign

/-- The generator `(0 1 i)` as an element of `Aₙ`. -/
private def gen (n : ℕ) [NeZero n] (hn : 2 ≤ n) (i : Fin n) (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
    alternatingGroup (Fin n) :=
  ⟨genPerm n i, genPerm_mem_alternatingGroup hn hi0 hi1⟩

/-- The support of the generator `(0 1 i)` is `{0, 1, i}`. -/
private theorem genPerm_support {n : ℕ} [NeZero n] (hn : 2 ≤ n) {i : Fin n}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
    (genPerm n i).support = ({0, 1, i} : Finset (Fin n)) := by
  -- (0 1 i) = swap 0 1 * swap 1 i = swap 0 i * swap 0 1, whose support is {0, 1, i}
  have h01 : (0 : Fin n) ≠ 1 := fin_one_ne_zero hn |>.symm
  have h0i : (0 : Fin n) ≠ i := hi0.symm
  have h1i : (1 : Fin n) ≠ i := hi1.symm
  have hswap : genPerm n i = Equiv.swap (0 : Fin n) i * Equiv.swap (0 : Fin n) 1 := by
    ext x
    -- swap 0 1 * swap 1 i = swap 0 i * swap 0 1 as (0 1 i) = (0 i 1)⁻¹-style rotation
    simp only [genPerm, Equiv.Perm.mul_apply]
    by_cases hx : x ∈ ({0, 1, i} : Finset (Fin n))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> grind
    · have hx0 : x ≠ (0 : Fin n) := by intro h; exact hx (by simp [h])
      have hx1 : x ≠ (1 : Fin n) := by intro h; exact hx (by simp [h])
      have hxi : x ≠ i := by intro h; exact hx (by simp [h])
      grind
  rw [hswap]
  apply Finset.ext
  intro x
  rw [support_swap_mul_swap_same h0i h01 hi1]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The product of two generators `(0 1 i)(0 1 j)` is the double transposition
`(0 i)(1 j)`; in particular it has order 2. -/
private theorem gen_mul_order2 {n : ℕ} [NeZero n] (hn : 3 ≤ n) {i j : Fin n}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hj0 : j ≠ 0) (hj1 : j ≠ 1) (hij : i ≠ j) :
    orderOf (genPerm n i * genPerm n j) = 2 := by
  have h01 : (0 : Fin n) ≠ 1 := fin_one_ne_zero (by omega) |>.symm
  have h0i : (0 : Fin n) ≠ i := hi0.symm
  have h1i : (1 : Fin n) ≠ i := hi1.symm
  have h0j : (0 : Fin n) ≠ j := hj0.symm
  have h1j : (1 : Fin n) ≠ j := hj1.symm
  have hprod : genPerm n i * genPerm n j = Equiv.swap (0 : Fin n) i * Equiv.swap 1 j := by
    simpa [genPerm] using
      (P_same (a := (0 : Fin n)) (b := (1 : Fin n)) (c := i) (d := j) h01 h0i h1i h0j h1j hij)
  have hsq : (genPerm n i * genPerm n j) * (genPerm n i * genPerm n j) = 1 := by
    rw [hprod]
    ext x
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    by_cases hx : x ∈ ({0, i, 1, j} : Finset (Fin n))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> grind
    · have hx0 : x ≠ (0 : Fin n) := by intro h; exact hx (by simp [h])
      have hxi : x ≠ i := by intro h; exact hx (by simp [h])
      have hx1 : x ≠ (1 : Fin n) := by intro h; exact hx (by simp [h])
      have hxj : x ≠ j := by intro h; exact hx (by simp [h])
      grind
  have hne : genPerm n i * genPerm n j ≠ 1 := by
    intro h
    have hx := congrArg (fun t : Equiv.Perm (Fin n) => t (0 : Fin n)) h
    rw [hprod] at hx
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at hx
    rw [Equiv.swap_apply_of_ne_of_ne h01 h0j, Equiv.swap_apply_left] at hx
    exact hi0 hx
  have : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime hsq hne

/-- The two generators `(0 1 i)` and `(0 1 j)` are distinct for `i ≠ j`. -/
private theorem genPerm_ne {n : ℕ} [NeZero n] (hn : 3 ≤ n) {i j : Fin n}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hj0 : j ≠ 0) (hj1 : j ≠ 1) (hij : i ≠ j) :
    genPerm n i ≠ genPerm n j := by
  intro h
  apply hij
  -- the two 3-cycles have different supports: {0, 1, i} vs {0, 1, j}
  have hsupp := congrArg (fun t : Equiv.Perm (Fin n) => t.support) h
  have hsi : (genPerm n i).support = ({0, 1, i} : Finset (Fin n)) := genPerm_support (by omega) hi0 hi1
  have hsj : (genPerm n j).support = ({0, 1, j} : Finset (Fin n)) := genPerm_support (by omega) hj0 hj1
  rw [hsi, hsj] at hsupp
  -- i ∈ {0, 1, j} would contradict hij and the hypotheses
  have hi_in : i ∈ ({0, 1, j} : Finset (Fin n)) := by
    rw [← hsupp]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi_in
  rcases hi_in with hi0' | hi1' | hij'
  · exact (hi0 hi0').elim
  · exact (hi1 hi1').elim
  · exact (hij hij').elim

/-- A generator is not the inverse of another: `(0 1 i) ≠ (0 1 j)⁻¹` for `i ≠ j`. -/
private theorem genPerm_ne_inv {n : ℕ} [NeZero n] (hn : 3 ≤ n) {i j : Fin n}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hj0 : j ≠ 0) (hj1 : j ≠ 1) (hij : i ≠ j) :
    genPerm n i ≠ (genPerm n j)⁻¹ := by
  intro h
  have h1 : genPerm n i * genPerm n j = 1 := by
    rw [h]
    simp
  have hord : orderOf (genPerm n i * genPerm n j) = 2 :=
    gen_mul_order2 (by omega) hi0 hi1 hj0 hj1 hij
  rw [h1] at hord
  norm_num at hord

/- The main theorem -/

/-! ### Milestone 4: `Aₙ` is generated by the `(0 1 i)` -/

/-- Disjoint transpositions commute. -/
private theorem swap_commute_disjoint {α : Type*} [DecidableEq α] {a b c d : α}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b := by
  ext x
  by_cases hx : x ∈ ({a, b, c, d} : Finset α)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp only [Equiv.Perm.mul_apply] <;> grind
  · have hxa : x ≠ a := by intro h; exact hx (by simp [h])
    have hxb : x ≠ b := by intro h; exact hx (by simp [h])
    have hxc : x ≠ c := by intro h; exact hx (by simp [h])
    have hxd : x ≠ d := by intro h; exact hx (by simp [h])
    simp only [Equiv.Perm.mul_apply]
    grind

/-- `(0 i 1) = (0 1 i)²`. -/
private theorem W2 {n : ℕ} [NeZero n] {i : Fin n} (hn : 2 ≤ n)
    (h0i : (0 : Fin n) ≠ i) (h1i : (1 : Fin n) ≠ i) :
    Equiv.swap (0 : Fin n) i * Equiv.swap i 1 = genPerm n i * genPerm n i := by
  have hg : (genPerm n i).IsThreeCycle := genPerm_isThreeCycle hn h0i.symm h1i.symm
  have h10 : (1 : Fin n) ≠ 0 := fin_one_ne_zero hn
  calc
    Equiv.swap (0 : Fin n) i * Equiv.swap i 1 = Equiv.swap 1 i * Equiv.swap (0 : Fin n) 1 := by
      ext x
      by_cases hx : x ∈ ({0, 1, i} : Finset (Fin n))
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> simp only [Equiv.Perm.mul_apply] <;> grind
      · have hx0 : x ≠ (0 : Fin n) := by intro h; exact hx (by simp [h])
        have hx1 : x ≠ (1 : Fin n) := by intro h; exact hx (by simp [h])
        have hxi : x ≠ i := by intro h; exact hx (by simp [h])
        simp only [Equiv.Perm.mul_apply]
        grind
    _ = (genPerm n i)⁻¹ := by
      change Equiv.swap 1 i * Equiv.swap (0 : Fin n) 1 = (Equiv.swap (0 : Fin n) 1 * Equiv.swap 1 i)⁻¹
      rw [mul_inv_rev]
      simp
    _ = genPerm n i * genPerm n i := threeCycle_inv_eq_sq hg

/-- The product of two generators is the double transposition `(0 x)(1 y)`. -/
private theorem gen_mul_double {n : ℕ} [NeZero n] {x y : Fin n}
    (h01 : (0 : Fin n) ≠ 1) (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hy0 : y ≠ 0) (hy1 : y ≠ 1)
    (hxy : x ≠ y) : genPerm n x * genPerm n y = Equiv.swap (0 : Fin n) x * Equiv.swap 1 y := by
  simpa [genPerm] using (P_same (a := (0 : Fin n)) (b := (1 : Fin n)) (c := x) (d := y)
    h01 hx0.symm hx1.symm hy0.symm hy1.symm hxy)

/-- `(0 j)(1 b)(0 i)(1 b) = (0 j)(0 i)`. -/
private theorem W3b {n : ℕ} [NeZero n] {i j b : Fin n}
    (h01 : (0 : Fin n) ≠ 1) (h1i : (1 : Fin n) ≠ i)
    (hb0 : b ≠ (0 : Fin n)) (hbi : b ≠ i) :
    (Equiv.swap (0 : Fin n) j * Equiv.swap 1 b) * (Equiv.swap (0 : Fin n) i * Equiv.swap 1 b) =
      Equiv.swap (0 : Fin n) j * Equiv.swap (0 : Fin n) i := by
  calc
    (Equiv.swap (0 : Fin n) j * Equiv.swap 1 b) * (Equiv.swap (0 : Fin n) i * Equiv.swap 1 b) =
        Equiv.swap (0 : Fin n) j * ((Equiv.swap 1 b * Equiv.swap (0 : Fin n) i) * Equiv.swap 1 b) := by
      group
    _ = Equiv.swap (0 : Fin n) j * ((Equiv.swap (0 : Fin n) i * Equiv.swap 1 b) * Equiv.swap 1 b) := by
      congr 1
      exact congrArg (fun t : Equiv.Perm (Fin n) => t * Equiv.swap 1 b)
        (swap_commute_disjoint (a := (1 : Fin n)) (b := b) (c := (0 : Fin n)) (d := i)
          h01.symm h1i hb0 hbi)
    _ = Equiv.swap (0 : Fin n) j * Equiv.swap (0 : Fin n) i := by
      rw [mul_swap_mul_self]

/-- `(0 j)(0 i) = (0 i j)` as swap products. -/
private theorem W3c {n : ℕ} [NeZero n] {i j : Fin n} (h0i : (0 : Fin n) ≠ i)
    (h0j : (0 : Fin n) ≠ j) (hij : i ≠ j) :
    Equiv.swap (0 : Fin n) j * Equiv.swap (0 : Fin n) i =
      Equiv.swap (0 : Fin n) i * Equiv.swap i j := by
  ext x
  by_cases hx : x ∈ ({0, i, j} : Finset (Fin n))
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp only [Equiv.Perm.mul_apply] <;> grind
  · have hx0 : x ≠ (0 : Fin n) := by intro h; exact hx (by simp [h])
    have hxi : x ≠ i := by intro h; exact hx (by simp [h])
    have hxj : x ≠ j := by intro h; exact hx (by simp [h])
    simp only [Equiv.Perm.mul_apply]
    grind

/-- `(0 i j) = (0 1 j)(0 1 b)(0 1 i)(0 1 b)` for `b` outside `{0, 1, i, j}`. -/
private theorem W3 {n : ℕ} [NeZero n] {i j b : Fin n}
    (h01 : (0 : Fin n) ≠ 1) (h0i : (0 : Fin n) ≠ i) (h1i : (1 : Fin n) ≠ i)
    (h0j : (0 : Fin n) ≠ j) (h1j : (1 : Fin n) ≠ j) (hij : i ≠ j)
    (hb0 : b ≠ (0 : Fin n)) (hb1 : b ≠ (1 : Fin n)) (hbi : b ≠ i) (hbj : b ≠ j) :
    Equiv.swap (0 : Fin n) i * Equiv.swap i j =
      genPerm n j * genPerm n b * genPerm n i * genPerm n b := by
  calc
    Equiv.swap (0 : Fin n) i * Equiv.swap i j =
        Equiv.swap (0 : Fin n) j * Equiv.swap (0 : Fin n) i := (W3c h0i h0j hij).symm
    _ = (Equiv.swap (0 : Fin n) j * Equiv.swap 1 b) * (Equiv.swap (0 : Fin n) i * Equiv.swap 1 b) :=
        (W3b h01 h1i hb0 hbi).symm
    _ = genPerm n j * genPerm n b * genPerm n i * genPerm n b := by
      rw [← gen_mul_double h01 h0j.symm h1j.symm hb0 hb1 hbj.symm]
      rw [← gen_mul_double h01 h0i.symm h1i.symm hb0 hb1 hbi.symm]
      group

/-- `(i j k) = (0 i j)(0 j k)` for `i, j, k ≥ 2` distinct. -/
private theorem W5 {n : ℕ} [NeZero n] {i j k : Fin n}
    (h0i : (0 : Fin n) ≠ i) (h0j : (0 : Fin n) ≠ j) (h0k : (0 : Fin n) ≠ k)
    (h1i : (1 : Fin n) ≠ i) (h1j : (1 : Fin n) ≠ j) (h1k : (1 : Fin n) ≠ k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Equiv.swap i j * Equiv.swap j k =
      (Equiv.swap (0 : Fin n) i * Equiv.swap i j) * (Equiv.swap (0 : Fin n) j * Equiv.swap j k) := by
  ext x
  by_cases hx : x ∈ ({0, i, j, k} : Finset (Fin n))
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp only [Equiv.Perm.mul_apply] <;> grind
  · have hx0 : x ≠ (0 : Fin n) := by intro h; exact hx (by simp [h])
    have hxi : x ≠ i := by intro h; exact hx (by simp [h])
    have hxj : x ≠ j := by intro h; exact hx (by simp [h])
    have hxk : x ≠ k := by intro h; exact hx (by simp [h])
    simp only [Equiv.Perm.mul_apply]
    grind

/-- `(1 i j) = (0 1 j)² (0 1 i)` for `i, j ≥ 2` distinct. -/
private theorem W6 {n : ℕ} [NeZero n] {i j : Fin n} (h01 : (0 : Fin n) ≠ 1)
    (h1i : (1 : Fin n) ≠ i) (h1j : (1 : Fin n) ≠ j) (h0i : (0 : Fin n) ≠ i)
    (h0j : (0 : Fin n) ≠ j) (hij : i ≠ j) :
    Equiv.swap (1 : Fin n) i * Equiv.swap i j =
      (genPerm n j * genPerm n j) * genPerm n i := by
  calc
    Equiv.swap (1 : Fin n) i * Equiv.swap i j =
        (Equiv.swap (0 : Fin n) 1 * Equiv.swap 1 j) * (Equiv.swap (0 : Fin n) 1 * Equiv.swap 1 j) *
          (Equiv.swap (0 : Fin n) 1 * Equiv.swap 1 i) := by
      ext x
      by_cases hx : x ∈ ({0, 1, i, j} : Finset (Fin n))
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> simp only [Equiv.Perm.mul_apply] <;> grind
      · have hx0 : x ≠ (0 : Fin n) := by intro h; exact hx (by simp [h])
        have hx1 : x ≠ (1 : Fin n) := by intro h; exact hx (by simp [h])
        have hxi : x ≠ i := by intro h; exact hx (by simp [h])
        have hxj : x ≠ j := by intro h; exact hx (by simp [h])
        simp only [Equiv.Perm.mul_apply]
        grind
    _ = (genPerm n j * genPerm n j) * genPerm n i := by
      simp [genPerm]

/-! ### Milestone 4: the generators `(0 1 i)` generate `Aₙ` -/

/-- A finite set of size smaller than the ambient type misses a point. -/
private theorem exists_ne_of_card_lt {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (hs : s.card < Fintype.card α) : ∃ x : α, x ∉ s := by
  by_contra h
  push Not at h
  have hsu : s = Finset.univ := Finset.eq_univ_iff_forall.mpr h
  have hs' : s.card = Fintype.card α := by
    rw [hsu]
    simp
  omega

/-- For `n ≥ 5` and points `i, j ∉ {0, 1}` distinct, there is a point outside
`{0, 1, i, j}`. -/
private theorem exists_ne_card_four {n : ℕ} [NeZero n] (hn : 5 ≤ n) (i j : Fin n)
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hj0 : j ≠ 0) (hj1 : j ≠ 1) (hij : i ≠ j) :
    ∃ b : Fin n, b ≠ 0 ∧ b ≠ 1 ∧ b ≠ i ∧ b ≠ j := by
  have h01 : (0 : Fin n) ≠ 1 := fin_one_ne_zero (by omega) |>.symm
  have h1i : (1 : Fin n) ≠ i := hi1.symm
  have h1j : (1 : Fin n) ≠ j := hj1.symm
  have hcard : ({0, 1, i, j} : Finset (Fin n)).card = 4 := by
    calc
      ({0, 1, i, j} : Finset (Fin n)).card =
          ({1, i, j} : Finset (Fin n)).card + 1 :=
        Finset.card_insert_of_notMem (by simp [h01, hi0.symm, hj0.symm])
      _ = ({i, j} : Finset (Fin n)).card + 1 + 1 := by
        rw [Finset.card_insert_of_notMem (by simp [h1i, h1j])]
      _ = ({j} : Finset (Fin n)).card + 1 + 1 + 1 := by
        rw [Finset.card_insert_of_notMem (by simp [hij])]
      _ = 4 := by simp
  have hlt : ({0, 1, i, j} : Finset (Fin n)).card < Fintype.card (Fin n) := by
    rw [hcard]
    simp
    omega
  obtain ⟨b, hb⟩ := exists_ne_of_card_lt ({0, 1, i, j} : Finset (Fin n)) hlt
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · intro h; exact hb (by simp [h])
  · intro h; exact hb (by simp [h])
  · intro h; exact hb (by simp [h])
  · intro h; exact hb (by simp [h])

/-- Every 3-cycle belongs to the closure of the generators `(0 1 i)`. -/
private theorem isThreeCycle_mem_closure_gen {n : ℕ} [NeZero n] (hn : 5 ≤ n)
    {g : Perm (Fin n)} (hg : g.IsThreeCycle) :
    g ∈ Subgroup.closure (Set.range fun i : {i : Fin n // i ≠ 0 ∧ i ≠ 1} => genPerm n i.1) := by
  classical
  let S : Set (Perm (Fin n)) := Set.range fun i : {i : Fin n // i ≠ 0 ∧ i ≠ 1} => genPerm n i.1
  have hgen_mem : ∀ i : Fin n, i ≠ 0 → i ≠ 1 → genPerm n i ∈ Subgroup.closure S := by
    intro i hi0 hi1
    exact Subgroup.subset_closure (show genPerm n i ∈ S from ⟨⟨i, hi0, hi1⟩, rfl⟩)
  by_cases h0 : (0 : Fin n) ∈ g.support <;> by_cases h1 : (1 : Fin n) ∈ g.support
  · -- {0, 1} ⊆ support: g = (0 1 i) or g = (0 1 i)² for the third point i
    have hg0_0 : g 0 ≠ (0 : Fin n) := by
      simpa using (Equiv.Perm.mem_support.mp h0)
    by_cases hp1 : g 0 = (1 : Fin n)
    · -- g 0 = 1: g = (0 1 (g 1))
      have hg1_ne0 : g (1 : Fin n) ≠ (0 : Fin n) := by
        intro hg1
        have hge : g = 1 := by
          calc
            g = Equiv.swap (0 : Fin n) (g 0) * Equiv.swap (g 0) (g (g 0)) :=
              hg.eq_swap_mul_swap_iff_mem_support.mpr h0
            _ = Equiv.swap (0 : Fin n) 1 * Equiv.swap 1 (g (1 : Fin n)) := by rw [hp1]
            _ = 1 := by
              rw [hg1, swap_comm]
              exact Equiv.swap_mul_self (1 : Fin n) (0 : Fin n)
        exact hg.ne_one hge
      have hg1_ne1 : g (1 : Fin n) ≠ (1 : Fin n) := by
        simpa using (Equiv.Perm.mem_support.mp h1)
      have hgform : g = genPerm n (g 1) := by
        calc
          g = Equiv.swap (0 : Fin n) (g 0) * Equiv.swap (g 0) (g (g 0)) :=
            hg.eq_swap_mul_swap_iff_mem_support.mpr h0
          _ = Equiv.swap (0 : Fin n) 1 * Equiv.swap 1 (g (1 : Fin n)) := by rw [hp1]
          _ = genPerm n (g 1) := rfl
      rw [hgform]
      exact hgen_mem (g 1) hg1_ne0 hg1_ne1
    · -- g 0 ≠ 1: g = (0 (g 0) 1) = (0 1 (g 0))²
      have hgg0_1 : g (g 0) = (1 : Fin n) := by
        have hss : g.support = ({0, g 0, g (g 0)} : Finset (Fin n)) :=
          threeCycle_support_eq hg h0
        have h1mem : (1 : Fin n) ∈ ({0, g 0, g (g 0)} : Finset (Fin n)) := by
          rwa [← hss]
        simp only [Finset.mem_insert, Finset.mem_singleton] at h1mem
        rcases h1mem with h10 | h1p | h1q
        · exact (fin_one_ne_zero (by omega) h10).elim
        · exact (hp1 h1p.symm).elim
        · exact h1q.symm
      have hgform : g = genPerm n (g 0) * genPerm n (g 0) := by
        calc
          g = Equiv.swap (0 : Fin n) (g 0) * Equiv.swap (g 0) (g (g 0)) :=
            hg.eq_swap_mul_swap_iff_mem_support.mpr h0
          _ = Equiv.swap (0 : Fin n) (g 0) * Equiv.swap (g 0) (1 : Fin n) := by rw [hgg0_1]
          _ = genPerm n (g 0) * genPerm n (g 0) :=
            W2 (by omega) hg0_0.symm (by intro h; exact hp1 h.symm)
      rw [hgform]
      exact Subgroup.mul_mem _ (hgen_mem (g 0) hg0_0 hp1) (hgen_mem (g 0) hg0_0 hp1)
  · -- 0 ∈ support, 1 ∉: g = (0 p q) = gen q * gen b * gen p * gen b
    have hg0_0 : g 0 ≠ (0 : Fin n) := by
      simpa using (Equiv.Perm.mem_support.mp h0)
    have hg0_1 : g 0 ≠ (1 : Fin n) := by
      intro h
      exact h1 (by simpa [h] using (Equiv.Perm.apply_mem_support).2 h0)
    have hgg0_0 : g (g 0) ≠ (0 : Fin n) := by
      intro h
      have hss : g.support = ({0, g 0, g (g 0)} : Finset (Fin n)) :=
        threeCycle_support_eq hg h0
      have hcard : ({0, g 0, g (g 0)} : Finset (Fin n)).card = 3 := by
        rw [← hss, hg.card_support]
      have hc2 : ({0, g 0, g (g 0)} : Finset (Fin n)).card = 2 := by
        simp [h, hg0_0]
      omega
    have hgg0_1 : g (g 0) ≠ (1 : Fin n) := by
      intro h
      exact h1 (by simpa [h] using
        ((Equiv.Perm.apply_mem_support).2 ((Equiv.Perm.apply_mem_support).2 h0)))
    have hg0_gg0 : g 0 ≠ g (g 0) := by
      intro h
      exact (Equiv.Perm.mem_support.mp ((Equiv.Perm.apply_mem_support).2 h0)) h.symm
    obtain ⟨b, hb0, hb1, hb0g, hbgg0⟩ := exists_ne_card_four hn (g 0) (g (g 0)) hg0_0 hg0_1
      hgg0_0 hgg0_1 hg0_gg0
    have hgform : g = genPerm n (g (g 0)) * genPerm n b * genPerm n (g 0) * genPerm n b := by
      calc
        g = Equiv.swap (0 : Fin n) (g 0) * Equiv.swap (g 0) (g (g 0)) :=
          hg.eq_swap_mul_swap_iff_mem_support.mpr h0
        _ = genPerm n (g (g 0)) * genPerm n b * genPerm n (g 0) * genPerm n b :=
          W3 (h01 := fin_one_ne_zero (by omega) |>.symm) (h0i := hg0_0.symm) (h1i := hg0_1.symm)
          (h0j := hgg0_0.symm) (h1j := hgg0_1.symm) (hij := hg0_gg0)
          (hb0 := hb0) (hb1 := hb1) (hbi := hb0g) (hbj := hbgg0)
    rw [hgform]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (hgen_mem (g (g 0)) hgg0_0 hgg0_1) (hgen_mem b hb0 hb1))
      (hgen_mem (g 0) hg0_0 hg0_1)) (hgen_mem b hb0 hb1)
  · -- 1 ∈ support, 0 ∉: g = (1 p q) = gen q² * gen p
    have hg1_1 : g 1 ≠ (1 : Fin n) := by
      simpa using (Equiv.Perm.mem_support.mp h1)
    have hg1_0 : g 1 ≠ (0 : Fin n) := by
      intro h
      exact h0 (by simpa [h] using (Equiv.Perm.apply_mem_support).2 h1)
    have hgg1_0 : g (g 1) ≠ (0 : Fin n) := by
      intro h
      exact h0 (by simpa [h] using
        ((Equiv.Perm.apply_mem_support).2 ((Equiv.Perm.apply_mem_support).2 h1)))
    have hgg1_1 : g (g 1) ≠ (1 : Fin n) := by
      intro h
      have hss : g.support = ({1, g 1, g (g 1)} : Finset (Fin n)) :=
        threeCycle_support_eq hg h1
      have hcard : ({1, g 1, g (g 1)} : Finset (Fin n)).card = 3 := by
        rw [← hss, hg.card_support]
      have hc2 : ({1, g 1, g (g 1)} : Finset (Fin n)).card = 2 := by
        simp [h, hg1_1]
      omega
    have hg1_gg1 : g 1 ≠ g (g 1) := by
      intro h
      exact (Equiv.Perm.mem_support.mp ((Equiv.Perm.apply_mem_support).2 h1)) h.symm
    have hgform : g = (genPerm n (g (g 1)) * genPerm n (g (g 1))) * genPerm n (g 1) := by
      calc
        g = Equiv.swap (1 : Fin n) (g 1) * Equiv.swap (g 1) (g (g 1)) :=
          hg.eq_swap_mul_swap_iff_mem_support.mpr h1
        _ = (genPerm n (g (g 1)) * genPerm n (g (g 1))) * genPerm n (g 1) :=
          W6 (h01 := fin_one_ne_zero (by omega) |>.symm) (h1i := hg1_1.symm) (h1j := hgg1_1.symm)
          (h0i := hg1_0.symm) (h0j := hgg1_0.symm) (hij := hg1_gg1)
    rw [hgform]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hgen_mem (g (g 1)) hgg1_0 hgg1_1)
      (hgen_mem (g (g 1)) hgg1_0 hgg1_1)) (hgen_mem (g 1) hg1_0 hg1_1)
  · -- 0, 1 ∉ support: g = (a p q) = (0 a p)(0 p q) with W3 decompositions
    have hne : g.support.Nonempty := by
      rw [← Finset.card_pos, hg.card_support]
      norm_num
    obtain ⟨a, ha⟩ := hne
    have ha_0 : a ≠ (0 : Fin n) := by
      intro ha0
      exact h0 (by simpa [ha0] using ha)
    have ha_1 : a ≠ (1 : Fin n) := by
      intro ha1
      exact h1 (by simpa [ha1] using ha)
    have ha_g : a ≠ g a := by
      intro h
      exact (Equiv.Perm.mem_support.mp ha) h.symm
    have ha_gg : a ≠ g (g a) := by
      intro hag
      have hss : g.support = ({a, g a, g (g a)} : Finset (Fin n)) :=
        threeCycle_support_eq hg ha
      have hcard : ({a, g a, g (g a)} : Finset (Fin n)).card = 3 := by
        rw [← hss, hg.card_support]
      have hsub : ({a, g a, g (g a)} : Finset (Fin n)) ⊆ ({a, g a} : Finset (Fin n)) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact Or.inl hag.symm
      have hle2 : ({a, g a} : Finset (Fin n)).card ≤ 2 := by
        calc
          ({a, g a} : Finset (Fin n)).card ≤ ({g a} : Finset (Fin n)).card + 1 :=
            Finset.card_insert_le a ({g a} : Finset (Fin n))
          _ ≤ 2 := by simp
      have : 3 ≤ 2 := by
        calc
          3 = ({a, g a, g (g a)} : Finset (Fin n)).card := hcard.symm
          _ ≤ ({a, g a} : Finset (Fin n)).card := Finset.card_le_card hsub
          _ ≤ 2 := hle2
      omega
    have hga_0 : g a ≠ (0 : Fin n) := by
      intro h
      exact h0 (by simpa [h] using (Equiv.Perm.apply_mem_support).2 ha)
    have hga_1 : g a ≠ (1 : Fin n) := by
      intro h
      exact h1 (by simpa [h] using (Equiv.Perm.apply_mem_support).2 ha)
    have hgga_0 : g (g a) ≠ (0 : Fin n) := by
      intro h
      exact h0 (by simpa [h] using
        ((Equiv.Perm.apply_mem_support).2 ((Equiv.Perm.apply_mem_support).2 ha)))
    have hgga_1 : g (g a) ≠ (1 : Fin n) := by
      intro h
      exact h1 (by simpa [h] using
        ((Equiv.Perm.apply_mem_support).2 ((Equiv.Perm.apply_mem_support).2 ha)))
    have hga_gga : g a ≠ g (g a) := by
      intro h
      exact (Equiv.Perm.mem_support.mp ((Equiv.Perm.apply_mem_support).2 ha)) h.symm
    obtain ⟨b, hb0, hb1, hba, hbga⟩ := exists_ne_card_four hn a (g a) ha_0 ha_1 hga_0 hga_1 ha_g
    obtain ⟨b', hb'0, hb'1, hb'ga, hb'gga⟩ := exists_ne_card_four hn (g a) (g (g a)) hga_0 hga_1
      hgga_0 hgga_1 hga_gga
    have hgform : g = (genPerm n (g a) * genPerm n b * genPerm n a * genPerm n b) *
        (genPerm n (g (g a)) * genPerm n b' * genPerm n (g a) * genPerm n b') := by
      calc
        g = Equiv.swap a (g a) * Equiv.swap (g a) (g (g a)) :=
          hg.eq_swap_mul_swap_iff_mem_support.mpr ha
        _ = (Equiv.swap (0 : Fin n) a * Equiv.swap a (g a)) *
            (Equiv.swap (0 : Fin n) (g a) * Equiv.swap (g a) (g (g a))) :=
          W5 (h0i := ha_0.symm) (h0j := hga_0.symm) (h0k := hgga_0.symm)
          (h1i := ha_1.symm) (h1j := hga_1.symm) (h1k := hgga_1.symm)
          (hij := ha_g) (hik := ha_gg) (hjk := hga_gga)
        _ = (genPerm n (g a) * genPerm n b * genPerm n a * genPerm n b) *
            (genPerm n (g (g a)) * genPerm n b' * genPerm n (g a) * genPerm n b') := by
          rw [W3 (h01 := fin_one_ne_zero (by omega) |>.symm) (h0i := ha_0.symm) (h1i := ha_1.symm)
            (h0j := hga_0.symm) (h1j := hga_1.symm) (hij := ha_g)
            (hb0 := hb0) (hb1 := hb1) (hbi := hba) (hbj := hbga),
            W3 (h01 := fin_one_ne_zero (by omega) |>.symm) (h0i := hga_0.symm) (h1i := hga_1.symm)
            (h0j := hgga_0.symm) (h1j := hgga_1.symm) (hij := hga_gga)
            (hb0 := hb'0) (hb1 := hb'1) (hbi := hb'ga) (hbj := hb'gga)]
    rw [hgform]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (hgen_mem (g a) hga_0 hga_1) (hgen_mem b hb0 hb1))
      (hgen_mem a ha_0 ha_1)) (hgen_mem b hb0 hb1))
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (hgen_mem (g (g a)) hgga_0 hgga_1) (hgen_mem b' hb'0 hb'1))
        (hgen_mem (g a) hga_0 hga_1)) (hgen_mem b' hb'0 hb'1))

/-- The generators `(0 1 i)` generate `Aₙ`. -/
private theorem gen_closure_eq_alternatingGroup {n : ℕ} [NeZero n] (hn : 5 ≤ n) :
    Subgroup.closure (Set.range fun i : {i : Fin n // i ≠ 0 ∧ i ≠ 1} => genPerm n i.1) =
      alternatingGroup (Fin n) := by
  apply le_antisymm
  · exact (Subgroup.closure_le (alternatingGroup (Fin n))).mpr (by
      intro g hg
      rcases hg with ⟨i, rfl⟩
      exact genPerm_mem_alternatingGroup (by omega) i.2.1 i.2.2)
  · calc
      alternatingGroup (Fin n) =
          Subgroup.closure ({σ : Perm (Fin n) | σ.IsThreeCycle} : Set (Perm (Fin n))) :=
        (Equiv.Perm.closure_three_cycles_eq_alternating (α := Fin n)).symm
      _ ≤ Subgroup.closure (Set.range fun i : {i : Fin n // i ≠ 0 ∧ i ≠ 1} => genPerm n i.1) := by
        exact (Subgroup.closure_le
          (Subgroup.closure (Set.range fun i : {i : Fin n // i ≠ 0 ∧ i ≠ 1} => genPerm n i.1))).mpr (by
          intro g hg
          exact isThreeCycle_mem_closure_gen hn hg)

/-- Transfer: a set of permutations inside `Aₙ` that generates `Aₙ` generates the
subgroup `Aₙ` as well. -/
private theorem closure_alternatingGroup_eq_top_of_generates {n : ℕ} [NeZero n]
    {S : Set (Perm (Fin n))} (hS : S ⊆ alternatingGroup (Fin n))
    (hgen : Subgroup.closure S = alternatingGroup (Fin n)) :
    (Subgroup.closure (Subtype.val ⁻¹' S) : Subgroup (alternatingGroup (Fin n))) = ⊤ := by
  let f : alternatingGroup (Fin n) →* Perm (Fin n) :=
    Subgroup.subtype (alternatingGroup (Fin n))
  let K : Subgroup (alternatingGroup (Fin n)) := Subgroup.closure (Subtype.val ⁻¹' S)
  -- every element of `S` lies in the image of `K` under the inclusion
  have hSimg : S ⊆ (Subgroup.map f K : Set (Perm (Fin n))) := by
    intro y hy
    exact Subgroup.mem_map.mpr
      ⟨⟨y, hS hy⟩, Subgroup.subset_closure (show ⟨y, hS hy⟩ ∈ Subtype.val ⁻¹' S from hy), rfl⟩
  have hle : Subgroup.closure S ≤ Subgroup.map f K :=
    (Subgroup.closure_le (Subgroup.map f K)).mpr hSimg
  apply le_antisymm
  · exact le_top
  · intro x hx
    have hxperm : (x : Perm (Fin n)) ∈ Subgroup.closure S := by
      rw [hgen]
      exact x.2
    have hximg : (x : Perm (Fin n)) ∈ Subgroup.map f K := hle hxperm
    rcases (Subgroup.mem_map.mp hximg) with ⟨k, hk, hfk⟩
    have hkx : k = x := by
      apply Subtype.ext
      exact hfk
    rwa [← hkx]

/-- The generators `(0 1 i)` generate the whole of `Aₙ` as a subgroup. -/
private theorem gen_closure_alternatingGroup_eq_top {n : ℕ} [NeZero n] (hn : 5 ≤ n) :
    (Subgroup.closure (Set.range fun i : {i : Fin n // i ≠ 0 ∧ i ≠ 1} =>
      (gen n (by omega) i.1 i.2.1 i.2.2 : alternatingGroup (Fin n))) :
      Subgroup (alternatingGroup (Fin n))) = ⊤ := by
  have hS : (Set.range fun i : {i : Fin n // i ≠ 0 ∧ i ≠ 1} => genPerm n i.1) ⊆
      alternatingGroup (Fin n) := by
    intro g hg
    rcases hg with ⟨i, rfl⟩
    exact genPerm_mem_alternatingGroup (by omega) i.2.1 i.2.2
  have hpre : (Subtype.val ⁻¹' Set.range fun i : {i : Fin n // i ≠ 0 ∧ i ≠ 1} => genPerm n i.1) =
      Set.range fun i : {i : Fin n // i ≠ 0 ∧ i ≠ 1} =>
        (gen n (by omega) i.1 i.2.1 i.2.2 : alternatingGroup (Fin n)) := by
    ext a
    constructor
    · intro ha
      rcases ha with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hi
    · intro ha
      rcases ha with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      change (gen n (by omega) i.1 i.2.1 i.2.2 : Perm (Fin n)) = (a : Perm (Fin n))
      exact congrArg (fun x : alternatingGroup (Fin n) => (x : Perm (Fin n))) hi
  rw [← hpre]
  exact closure_alternatingGroup_eq_top_of_generates hS (gen_closure_eq_alternatingGroup hn)

/- The main theorem -/

/-- The kernel of the conjugation action on a normal subgroup is its
centralizer in the ambient group. -/
private theorem conjNormal_ker_local {G : Type u} [Group G]
    {K : Subgroup G} [K.Normal] :
    (MulAut.conjNormal (H := K)).ker = Subgroup.centralizer (K : Set G) := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hfix : MulAut.conjNormal x ⟨k, hk⟩ = ⟨k, hk⟩ := by
      have hfix' := congrArg (fun e : MulAut K => e ⟨k, hk⟩) hx
      rw [MulAut.one_apply] at hfix'
      exact hfix'
    have hconj : x * k * x⁻¹ = k :=
      (MulAut.conjNormal_apply x ⟨k, hk⟩).symm.trans
        (congrArg Subtype.val hfix)
    calc
      k * x = (x * k * x⁻¹) * x := by rw [hconj]
      _ = x * k := by simp [mul_assoc]
  · intro hx
    ext k
    rw [MulAut.conjNormal_apply, MulAut.one_apply]
    have hx' : (k : G) * x = x * (k : G) :=
      (Subgroup.mem_centralizer_iff.mp hx) (k : G) k.2
    calc
      x * (k : G) * x⁻¹ = ((k : G) * x) * x⁻¹ := by rw [hx']
      _ = (k : G) := by simp [mul_assoc]

/-- The conjugation map `Sₙ → Aut(Aₙ)` is injective for `n ≥ 4`. -/
public theorem conjNormal_injective_alternatingGroup (n : ℕ) (hn : 4 ≤ n) :
    Function.Injective (MulAut.conjNormal (H := alternatingGroup (Fin n)) :
      Perm (Fin n) →* MulAut (alternatingGroup (Fin n))) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [conjNormal_ker_local]
  exact centralizer_alternatingGroup_eq_bot n (by omega)

/-- An automorphism of `Aₙ` preserving the class of 3-cycles is conjugation by a
permutation of the point set (`n ≥ 5`).  This is the surjectivity half of Theorem
5.2.1, isolated from the `n ≠ 6` class-size argument (`threeCycle_of_mulAut`); for
`n = 6` the hypothesis is supplied by composing with the exceptional automorphism. -/
private theorem aut_of_preserves_threeCycle (n : ℕ) (hn : 5 ≤ n)
    (φ : MulAut (alternatingGroup (Fin n)))
    (hφ : ∀ c : alternatingGroup (Fin n), (c : Perm (Fin n)).IsThreeCycle →
      ((φ c : alternatingGroup (Fin n)) : Perm (Fin n)).IsThreeCycle) :
    ∃ σ : Perm (Fin n),
      φ = MulAut.conjNormal (H := alternatingGroup (Fin n)) σ := by
  classical
  have : NeZero n := ⟨by omega⟩
  -- the images of the generators `(0 1 i)` under φ form a 3-cycle family
  let h : points_off n hn → Perm (Fin n) :=
    fun i => (φ (gen n (by omega) i.1 i.2.1 i.2.2) : Perm (Fin n))
  have h3c : ∀ i, (h i).IsThreeCycle := by
    intro i
    simpa [h, gen] using
      hφ (gen n (by omega) i.1 i.2.1 i.2.2) (genPerm_isThreeCycle (by omega) i.2.1 i.2.2)
  have hord : ∀ i j, i ≠ j → orderOf (h i * h j) = 2 := by
    intro i j hij
    have hne : i.1 ≠ j.1 := by
      intro h
      apply hij
      apply Subtype.ext
      exact h
    calc
      orderOf (h i * h j) =
          orderOf ((φ (gen n (by omega) i.1 i.2.1 i.2.2 * gen n (by omega) j.1 j.2.1 j.2.2) :
            alternatingGroup (Fin n)) : Perm (Fin n)) := by
        simp [h, map_mul, Subgroup.coe_mul]
      _ = orderOf (gen n (by omega) i.1 i.2.1 i.2.2 * gen n (by omega) j.1 j.2.1 j.2.2) := by
        rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      _ = 2 := by
        rw [← Subgroup.orderOf_coe]
        simpa [gen, Subgroup.coe_mul] using gen_mul_order2 (by omega) i.2.1 i.2.2 j.2.1 j.2.2 hne
  have hinj : Function.Injective h := by
    intro i j hij
    have hgi : (φ (gen n (by omega) i.1 i.2.1 i.2.2) : Perm (Fin n)) =
        (φ (gen n (by omega) j.1 j.2.1 j.2.2) : Perm (Fin n)) := by
      simpa [h] using hij
    have hg : gen n (by omega) i.1 i.2.1 i.2.2 = gen n (by omega) j.1 j.2.1 j.2.2 := by
      apply φ.injective
      apply Subtype.ext
      exact hgi
    have hperm : genPerm n i.1 = genPerm n j.1 := by
      simpa [gen] using congrArg (fun t : alternatingGroup (Fin n) => (t : Perm (Fin n))) hg
    have hne : i.1 = j.1 := by
      by_contra h
      exact genPerm_ne (by omega) i.2.1 i.2.2 j.2.1 j.2.2 h hperm
    apply Subtype.ext
    exact hne
  -- all images share a common pair `{a, b}`: φ((0 1 i)) = (a b (f i))
  obtain ⟨a, b, hab, f, hfne, hfinj, hfam⟩ := threeCycle_family n hn h3c hord hinj
  -- the induced permutation σ of the points
  let σ : Fin n → Fin n := fun i =>
    if h0 : i = (0 : Fin n) then a
    else if h1 : i = (1 : Fin n) then b
    else f ⟨i, h0, h1⟩
  have h10 : (1 : Fin n) ≠ (0 : Fin n) := fin_one_ne_zero (by omega)
  have hσinj : Function.Injective σ := by
    intro i j hij
    by_cases hi0 : i = (0 : Fin n)
    · rw [hi0] at hij ⊢
      by_cases hj0 : j = (0 : Fin n)
      · rw [hj0] at hij ⊢
      · by_cases hj1 : j = (1 : Fin n)
        · rw [hj1] at hij ⊢
          exfalso
          exact hab (by simpa [σ, h10] using hij)
        · exfalso
          exact (hfne ⟨j, hj0, hj1⟩).1 (by simpa [σ, hj0, hj1] using hij)
    · by_cases hi1 : i = (1 : Fin n)
      · rw [hi1] at hij ⊢
        by_cases hj0 : j = (0 : Fin n)
        · rw [hj0] at hij ⊢
          exfalso
          exact hab.symm (by simpa [σ, h10] using hij)
        · by_cases hj1 : j = (1 : Fin n)
          · rw [hj1] at hij ⊢
          · exfalso
            exact (hfne ⟨j, hj0, hj1⟩).2 (by simpa [σ, hj0, hj1, h10] using hij)
      · by_cases hj0 : j = (0 : Fin n)
        · rw [hj0] at hij ⊢
          exfalso
          exact (hfne ⟨i, hi0, hi1⟩).1 (by simpa [σ, hi0, hi1] using hij.symm)
        · by_cases hj1 : j = (1 : Fin n)
          · rw [hj1] at hij ⊢
            exfalso
            exact (hfne ⟨i, hi0, hi1⟩).2 (by simpa [σ, hi0, hi1, h10] using hij.symm)
          · have hf : f ⟨i, hi0, hi1⟩ = f ⟨j, hj0, hj1⟩ := by
              simpa [σ, hi0, hi1, hj0, hj1] using hij
            have hsub : (⟨i, hi0, hi1⟩ : points_off n hn) = ⟨j, hj0, hj1⟩ := hfinj hf
            simpa using congrArg (fun t : points_off n hn => t.1) hsub
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective hσinj
  let σe : Equiv.Perm (Fin n) := Equiv.ofBijective σ ⟨hσinj, hσsurj⟩
  have hσ0 : σe (0 : Fin n) = a := by
    simp [σe, σ]
  have hσ1 : σe (1 : Fin n) = b := by
    simp [σe, σ, h10]
  have hσi : ∀ i : points_off n hn, σe i.1 = f i := by
    intro i
    simp [σe, σ, i.2.1, i.2.2]
  -- φ agrees with conjugation by σe on the generators
  have hφσ : ∀ i : points_off n hn,
      φ (gen n (by omega) i.1 i.2.1 i.2.2) =
        MulAut.conjNormal (H := alternatingGroup (Fin n)) σe (gen n (by omega) i.1 i.2.1 i.2.2) := by
    intro i
    apply Subtype.ext
    calc
      (φ (gen n (by omega) i.1 i.2.1 i.2.2) : Perm (Fin n)) = h i := rfl
      _ = Equiv.swap a b * Equiv.swap b (f i) := hfam i
      _ = Equiv.swap (σe (0 : Fin n)) (σe (1 : Fin n)) *
          Equiv.swap (σe (1 : Fin n)) (σe i.1) := by
        rw [hσ0, hσ1, hσi]
      _ = σe * Equiv.swap (0 : Fin n) (1 : Fin n) * σe⁻¹ *
          (σe * Equiv.swap (1 : Fin n) i.1 * σe⁻¹) := by
        rw [← conj_swap σe (0 : Fin n) (1 : Fin n)]
        rw [← conj_swap σe (1 : Fin n) i.1]
      _ = σe * (Equiv.swap (0 : Fin n) (1 : Fin n) *
          Equiv.swap (1 : Fin n) i.1) * σe⁻¹ := by
        group
      _ = σe * genPerm n i.1 * σe⁻¹ := by
        simp [genPerm]
      _ = (MulAut.conjNormal (H := alternatingGroup (Fin n)) σe
          (gen n (by omega) i.1 i.2.1 i.2.2) : Perm (Fin n)) := by
        rw [MulAut.conjNormal_apply]
        simp [gen]
  -- the equalizer of φ and conjNormal σe contains the generators, hence all of Aₙ
  let E : Subgroup (alternatingGroup (Fin n)) :=
    { carrier := {x : alternatingGroup (Fin n) |
        φ x = MulAut.conjNormal (H := alternatingGroup (Fin n)) σe x}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        change φ (x * y) = MulAut.conjNormal (H := alternatingGroup (Fin n)) σe (x * y)
        rw [map_mul, hx, hy]
        simp
      inv_mem' := by
        intro x hx
        change φ (x⁻¹) = MulAut.conjNormal (H := alternatingGroup (Fin n)) σe (x⁻¹)
        rw [map_inv, hx]
        simp }
  have hgenE : Set.range (fun i : points_off n hn => gen n (by omega) i.1 i.2.1 i.2.2) ⊆
      (E : Set (alternatingGroup (Fin n))) := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    exact hφσ i
  have hEtop : E = ⊤ := by
    have hle : Subgroup.closure (Set.range fun i : points_off n hn =>
        (gen n (by omega) i.1 i.2.1 i.2.2 : alternatingGroup (Fin n))) ≤ E :=
      (Subgroup.closure_le E).mpr hgenE
    have hcl : (Subgroup.closure (Set.range fun i : points_off n hn =>
        (gen n (by omega) i.1 i.2.1 i.2.2 : alternatingGroup (Fin n))) :
        Subgroup (alternatingGroup (Fin n))) = ⊤ :=
      gen_closure_alternatingGroup_eq_top hn
    rw [hcl] at hle
    exact le_antisymm le_top hle
  -- φ = conjNormal σe, so the conjugation map is surjective on the
  -- class-preserving automorphisms
  refine ⟨σe, ?_⟩
  apply MulEquiv.ext
  intro x
  have hxE : x ∈ E := by
    rw [hEtop]
    trivial
  exact hxE

/-- GLS vol. 3, Theorem 5.2.1: for `n ≥ 5`, `n ≠ 6`, the conjugation map
`Sₙ → Aut(Aₙ)` is bijective.  (Surjectivity: Milestones 3–4 of
`task-aut-alternating.md`.) -/
public theorem aut_alternatingGroup_bijective_conj (n : ℕ) (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    Function.Bijective (MulAut.conjNormal (H := alternatingGroup (Fin n)) :
      Perm (Fin n) →* MulAut (alternatingGroup (Fin n))) := by
  refine ⟨conjNormal_injective_alternatingGroup n (by omega), ?_⟩
  -- surjectivity (Milestones 3–4): the automorphism maps the class of 3-cycles to
  -- itself (Milestone 3), hence is conjugation by a permutation (Milestone 4)
  intro φ
  have hφ : ∀ c : alternatingGroup (Fin n), (c : Perm (Fin n)).IsThreeCycle →
      ((φ c : alternatingGroup (Fin n)) : Perm (Fin n)).IsThreeCycle := by
    intro c hc
    exact threeCycle_of_mulAut n hn hn6 φ hc
  rcases aut_of_preserves_threeCycle n hn φ hφ with ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  exact hσ.symm


end AutAlternating

end CFSG.GroupTheory
