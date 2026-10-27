/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Isaacs, Finite Group Theory — Ch. 8: orbitals (Lem 8.34)

Formalizes the basics of the orbital theory of §8D and **Isaacs Lem 8.34**
(p. 244).  For a group `G` acting on `Ω`, the *orbitals* are the `G`-orbits
on `Ω × Ω` under the diagonal action, and the *orbital function* of a set
`Δ ⊆ Ω × Ω` at `α` is `Δ(α) = {β | (α, β) ∈ Δ}` (`orbitalAt`).

Lemma 8.34, in four statements:

* `orbital_eq_of_orbitalAt_inter` — the sets `Δ(α)` for distinct orbitals
  `Δ` are disjoint;
* `orbitalAt_orbit_eq` — `Δ(α)` for `Δ` the orbital of `(α, β)` is exactly
  the `G_α`-orbit of `β` (so, as `Δ` varies, the `Δ(α)` are exactly the
  suborbits at `α`);
* `orbitalAt_orbit_smul` — `Δ(g • α) = g • Δ(α)`;
* `card_orbit_eq_card_mul_card_orbitalAt` — `|Δ| = |Ω| · |Δ(α)|` for a
  transitive action on a finite set (the book's `|Δ(α)| = |Δ|/|Ω|`).
-/

public section

namespace CFSG

namespace FiveTransitive.OddOrder.Isaacs.Ch08

open MulAction

open scoped Pointwise

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- The orbital function of a set of pairs at a point:
`Δ(α) = {β | (α, β) ∈ Δ}`. -/
@[expose] def orbitalAt (Δ : Set (Ω × Ω)) (α : Ω) : Set Ω := {β | (α, β) ∈ Δ}

lemma mem_orbitalAt_iff {Δ : Set (Ω × Ω)} {α β : Ω} :
    β ∈ orbitalAt Δ α ↔ (α, β) ∈ Δ :=
  Iff.rfl

/-- Orbitals are `G`-invariant, pairwise. -/
lemma smul_pair_mem_orbit {p : Ω × Ω} (g : G) {a b : Ω}
    (h : (a, b) ∈ orbit G p) : (g • a, g • b) ∈ orbit G p := by
  have h2 := MulAction.smul_orbit g p ▸ Set.smul_mem_smul_set h
  rwa [Prod.smul_mk] at h2

/-- **Isaacs Lem 8.34**, disjointness — the orbital functions of distinct
orbitals at a common point are disjoint. -/
theorem orbital_eq_of_orbitalAt_inter {p q : Ω × Ω} {α β : Ω}
    (h₁ : β ∈ orbitalAt (orbit G p) α) (h₂ : β ∈ orbitalAt (orbit G q) α) :
    orbit G p = orbit G q := by
  rw [mem_orbitalAt_iff] at h₁ h₂
  rw [← orbit_eq_iff.mpr h₁, ← orbit_eq_iff.mpr h₂]

/-- **Isaacs Lem 8.34**, suborbits — the orbital function of the orbital of
`(α, β)` at `α` is the orbit of `β` under the stabilizer of `α`.  As `Δ`
runs over the orbitals, the `Δ(α)` are therefore exactly the suborbits
at `α`. -/
theorem orbitalAt_orbit_eq (α β : Ω) :
    orbitalAt (orbit G (α, β)) α = orbit (stabilizer G α) β := by
  ext γ
  rw [mem_orbitalAt_iff]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨hg1, hg2⟩ := Prod.mk_inj.mp hg
    exact ⟨⟨g, mem_stabilizer_iff.mpr hg1⟩, hg2⟩
  · rintro ⟨⟨g, hg⟩, rfl⟩
    refine ⟨g, Prod.ext ?_ rfl⟩
    exact mem_stabilizer_iff.mp hg

/-- **Isaacs Lem 8.34**, translation — `Δ(g • α) = g • Δ(α)` for an
orbital `Δ`. -/
theorem orbitalAt_orbit_smul (p : Ω × Ω) (g : G) (α : Ω) :
    orbitalAt (orbit G p) (g • α) = g • orbitalAt (orbit G p) α := by
  ext β
  rw [mem_orbitalAt_iff, Set.mem_smul_set_iff_inv_smul_mem, mem_orbitalAt_iff]
  have key : ∀ x : Ω × Ω, x ∈ orbit G p ↔ g • x ∈ orbit G p := by
    intro x
    constructor
    · intro hx
      exact MulAction.smul_orbit g p ▸ Set.smul_mem_smul_set hx
    · intro hx
      have h2 := Set.smul_mem_smul_set (a := g⁻¹) hx
      rwa [MulAction.smul_orbit, inv_smul_smul] at h2
  have hpair : (g • α, β) = g • (α, g⁻¹ • β) := by
    rw [Prod.smul_mk, smul_inv_smul]
  rw [hpair]
  exact (key _).symm

/-- **Isaacs Lem 8.34**, counting — for a transitive action on a finite
set, `|Δ| = |Ω| · |Δ(α)|` for every orbital `Δ` (the book's
`|Δ(α)| = |Δ|/|Ω|`; in particular `|Δ(α)|` is independent of `α`). -/
theorem card_orbit_eq_card_mul_card_orbitalAt [Finite Ω]
    [IsPretransitive G Ω] (p : Ω × Ω) (α : Ω) :
    Nat.card (orbit G p) =
      Nat.card Ω * Nat.card (orbitalAt (orbit G p) α) := by
  classical
  have := Fintype.ofFinite Ω
  set Δ : Set (Ω × Ω) := orbit G p with hΔ
  have hfiber : ∀ a : Ω,
      (Δ.toFinset.filter fun x => x.1 = a).card =
        Nat.card (orbitalAt Δ a) := by
    intro a
    rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
    apply Finset.card_bij (fun x _ => x.2)
    · rintro ⟨x1, x2⟩ hx
      simp only [Finset.mem_filter, Set.mem_toFinset] at hx
      obtain ⟨hxΔ, rfl⟩ := hx
      rw [Set.mem_toFinset]
      exact hxΔ
    · rintro ⟨x1, x2⟩ hx ⟨y1, y2⟩ hy h
      simp only [Finset.mem_filter, Set.mem_toFinset] at hx hy
      simp only at h
      exact Prod.ext (hx.2.trans hy.2.symm) h
    · intro b hb
      rw [Set.mem_toFinset] at hb
      refine ⟨(a, b), ?_, rfl⟩
      simp only [Finset.mem_filter, Set.mem_toFinset]
      exact ⟨hb, trivial⟩
  have hconst : ∀ a : Ω,
      Nat.card (orbitalAt Δ a) = Nat.card (orbitalAt Δ α) := by
    intro a
    obtain ⟨g, rfl⟩ := exists_smul_eq G α a
    rw [hΔ, orbitalAt_orbit_smul]
    have himg : (g • orbitalAt (orbit G p) α) =
        (fun β => g • β) '' orbitalAt (orbit G p) α := rfl
    rw [himg, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
      Set.ncard_image_of_injective _ (MulAction.injective g)]
  calc Nat.card ↥Δ
      = Δ.toFinset.card := by rw [Set.toFinset_card, Nat.card_eq_fintype_card]
    _ = ∑ a : Ω, (Δ.toFinset.filter fun x => x.1 = a).card := by
        exact Finset.card_eq_sum_card_fiberwise (f := fun x : Ω × Ω => x.1)
          (t := Finset.univ) fun x _ => Finset.mem_univ x.1
    _ = ∑ _a : Ω, Nat.card (orbitalAt Δ α) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hfiber a, hconst a]
    _ = Nat.card Ω * Nat.card (orbitalAt Δ α) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
          Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

end FiveTransitive.OddOrder.Isaacs.Ch08

end CFSG
