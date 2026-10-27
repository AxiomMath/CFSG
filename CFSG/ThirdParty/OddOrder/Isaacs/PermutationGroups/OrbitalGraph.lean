/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.Orbitals
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.Data.Fintype.Pigeonhole

/-!
# Isaacs, Finite Group Theory — Ch. 8: orbital graphs (Thm 8.35, Lem 8.36)

The orbital digraph of an orbital `Δ` has vertex set `Ω` and an arrow
`α → β` iff `(α, β) ∈ Δ`; path connectivity is
`Relation.ReflTransGen (fun a b => (a, b) ∈ Δ)`, and topological
connectivity uses the symmetrized relation.

* **Lem 8.36** (`reflTransGen_of_reflTransGen_or`): for a `G`-invariant
  relation on a finite set with `G` transitive (a vertex-transitive
  digraph), topological connectivity implies path connectivity — a reverse
  edge `β → α` yields the forward path
  `α = β·gⁿ → β·gⁿ⁻¹ → ⋯ → β·g = α·g⁻¹·g ⋯`;
* **Thm 8.35** (`isPreprimitive_of_orbital_connected`,
  `orbital_connected_of_isPreprimitive`): a transitive action is primitive
  iff every non-diagonal orbital graph is connected.
-/

public section

namespace CFSG

namespace FiveTransitive.OddOrder.Isaacs.Ch08

open MulAction

open scoped Pointwise

variable {G Ω : Type*} [Group G] [MulAction G Ω]

section Helpers

/-- Orbitals are `G`-invariant, pairwise. -/
private lemma mem_orbit_smul_pair {p : Ω × Ω} (g : G) {a b : Ω}
    (h : (a, b) ∈ orbit G p) : (g • a, g • b) ∈ orbit G p := by
  have h2 := MulAction.smul_orbit g p ▸ Set.smul_mem_smul_set h
  rwa [Prod.smul_mk] at h2

/-- Paths transport along the action for an invariant relation. -/
private lemma reflTransGen_smul {r : Ω → Ω → Prop}
    (hinv : ∀ (g : G) x y, r x y → r (g • x) (g • y)) (g : G) {a b : Ω}
    (h : Relation.ReflTransGen r a b) :
    Relation.ReflTransGen r (g • a) (g • b) := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail (hinv g _ _ hbc)

/-- The reflexive-transitive closure of a symmetric relation is
symmetric. -/
private lemma reflTransGen_or_symm {r : Ω → Ω → Prop} {a b : Ω}
    (h : Relation.ReflTransGen (fun x y => r x y ∨ r y x) a b) :
    Relation.ReflTransGen (fun x y => r x y ∨ r y x) b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact Relation.ReflTransGen.trans (.single hbc.symm) ih

/-- A path from inside `B` to outside `B` contains an edge leaving `B`. -/
lemma exists_exit {r : Ω → Ω → Prop} {B : Set Ω} {a b : Ω}
    (h : Relation.ReflTransGen r a b) (ha : a ∈ B) :
    b ∉ B → ∃ γ ∈ B, ∃ δ, δ ∉ B ∧ r γ δ := by
  induction h with
  | refl => intro hb; exact absurd ha hb
  | @tail c d h₁ h₂ ih =>
    intro hb
    by_cases hc : c ∈ B
    · exact ⟨c, hc, d, hb, h₂⟩
    · exact ih hc

end Helpers

section Lemma836

variable [Finite Ω] [IsPretransitive G Ω]

/-- **Isaacs Lem 8.36**, key step — for a `G`-invariant relation on a
finite `G`-transitive set, a reverse edge yields a forward path. -/
private lemma reflTransGen_of_rev {r : Ω → Ω → Prop}
    (hinv : ∀ (g : G) x y, r x y → r (g • x) (g • y))
    {α β : Ω} (h : r β α) : Relation.ReflTransGen r α β := by
  obtain ⟨g, hg⟩ := exists_smul_eq G α β
  -- a chain `g^(m+1) • α → g^m • α` of edges
  have hchain : ∀ k : ℕ, 1 ≤ k →
      Relation.ReflTransGen r (g ^ k • α) (g • α) := by
    intro k hk
    induction k with
    | zero => omega
    | succ m ih =>
      rcases Nat.lt_or_ge 1 (m + 1) with h1 | h1
      · have hm : 1 ≤ m := by omega
        have hedge : r (g ^ (m + 1) • α) (g ^ m • α) := by
          have h2 := hinv (g ^ m) β α h
          rwa [← hg, smul_smul, ← pow_succ] at h2
        exact Relation.ReflTransGen.head hedge (ih hm)
      · have hm0 : m = 0 := by omega
        subst hm0
        rw [pow_one]
    -- find `n ≥ 1` with `g ^ n • α = α` (finiteness)
  have hkey : ∀ {a b : ℕ}, a < b → g ^ a • α = g ^ b • α →
      g ^ (b - a) • α = α := by
    intro a b hab heq
    apply MulAction.injective (g ^ a)
    change g ^ a • g ^ (b - a) • α = g ^ a • α
    rw [smul_smul, ← pow_add, Nat.add_sub_cancel' (le_of_lt hab)]
    exact heq.symm
  obtain ⟨m, m', hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => g ^ k • α)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hn := hkey hlt heq
    have h2 := hchain (m' - m) (by omega)
    rwa [hn, hg] at h2
  · have hn := hkey hlt heq.symm
    have h2 := hchain (m - m') (by omega)
    rwa [hn, hg] at h2

/-- **Isaacs Lem 8.36** — for a `G`-invariant relation on a finite set with
`G` transitive (the orbital-graph setting: a vertex-transitive digraph),
topological connectivity implies path connectivity. -/
theorem reflTransGen_of_reflTransGen_or {r : Ω → Ω → Prop}
    (hinv : ∀ (g : G) x y, r x y → r (g • x) (g • y)) {α β : Ω}
    (h : Relation.ReflTransGen (fun x y => r x y ∨ r y x) α β) :
    Relation.ReflTransGen r α β := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih =>
    rcases hbc with h1 | h1
    · exact ih.tail h1
    · exact ih.trans (reflTransGen_of_rev hinv h1)

end Lemma836

section Theorem835

/-- **Isaacs Thm 8.35**, sufficiency — if the orbital graph of every
non-diagonal orbital is (path) connected, then the transitive action is
primitive. -/
theorem isPreprimitive_of_orbital_connected [IsPretransitive G Ω]
    (hconn : ∀ p : Ω × Ω, p.1 ≠ p.2 → ∀ x y : Ω,
      Relation.ReflTransGen (fun a b => (a, b) ∈ orbit G p) x y) :
    IsPreprimitive G Ω := by
  refine ⟨fun {B} hB => ?_⟩
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  right
  rw [Set.not_subsingleton_iff] at hsub
  obtain ⟨α, hα, β, hβ, hab⟩ := hsub
  rw [Set.eq_univ_iff_forall]
  by_contra hne
  obtain ⟨δ₀, hδ₀⟩ := not_forall.mp hne
  obtain ⟨γ, hγ, δ, hδ, hedge⟩ :=
    exists_exit (hconn (α, β) hab α δ₀) hα hδ₀
  obtain ⟨g, hg⟩ := hedge
  have hg' : g • (α, β) = (γ, δ) := hg
  rw [Prod.smul_mk, Prod.mk_inj] at hg'
  obtain ⟨hg1, hg2⟩ := hg'
  have hγ2 : γ ∈ g • B := hg1 ▸ Set.smul_mem_smul_set hα
  have heqB : g • B = B := by
    have h2 := hB.smul_eq_smul_of_nonempty (g₁ := g) (g₂ := 1)
      ⟨γ, hγ2, by rwa [one_smul]⟩
    rwa [one_smul] at h2
  exact hδ (hg2 ▸ heqB ▸ Set.smul_mem_smul_set hβ)

/-- **Isaacs Thm 8.35**, necessity — for a primitive action on a finite
set, the orbital graph of every non-diagonal orbital is (path)
connected. -/
theorem orbital_connected_of_isPreprimitive [Finite Ω] [IsPreprimitive G Ω]
    {p : Ω × Ω} (hp : p.1 ≠ p.2) (x y : Ω) :
    Relation.ReflTransGen (fun a b => (a, b) ∈ orbit G p) x y := by
  have hinv : ∀ (g : G) (a b : Ω), (a, b) ∈ orbit G p →
      (g • a, g • b) ∈ orbit G p := fun g a b h => mem_orbit_smul_pair g h
  apply reflTransGen_of_reflTransGen_or (G := G) hinv
  -- the topological component of `x` is a block
  set r : Ω → Ω → Prop :=
    fun a b => (a, b) ∈ orbit G p ∨ (b, a) ∈ orbit G p with hr
  set B : Set Ω := {z | Relation.ReflTransGen r x z} with hBdef
  have hinvr : ∀ (g : G) (a b : Ω), r a b → r (g • a) (g • b) := by
    rintro g a b (h | h)
    · exact Or.inl (mem_orbit_smul_pair g h)
    · exact Or.inr (mem_orbit_smul_pair g h)
  have hcomp : ∀ g : G, g • B = {z | Relation.ReflTransGen r (g • x) z} := by
    intro g
    ext z
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    constructor
    · intro hz
      have h2 := reflTransGen_smul hinvr g hz
      rwa [smul_inv_smul] at h2
    · intro hz
      have h2 := reflTransGen_smul hinvr g⁻¹ hz
      rwa [inv_smul_smul] at h2
  have hblock : IsBlock G B := by
    rw [isBlock_iff_smul_eq_smul_of_nonempty]
    rintro g₁ g₂ ⟨z, hz1, hz2⟩
    rw [hcomp] at hz1 hz2 ⊢
    rw [hcomp]
    have hpath : Relation.ReflTransGen r (g₁ • x) (g₂ • x) :=
      Relation.ReflTransGen.trans hz1 (reflTransGen_or_symm hz2)
    ext w
    exact ⟨fun hw => Relation.ReflTransGen.trans
        (reflTransGen_or_symm hpath) hw,
      fun hw => Relation.ReflTransGen.trans hpath hw⟩
  -- `B` contains `x` and a neighbor, so it is not a subsingleton
  have hxB : x ∈ B := Relation.ReflTransGen.refl
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq G p.1 x
  have hnb : (x, g₀ • p.2) ∈ orbit G p := by
    have h2 := mem_orbit_smul_pair (p := p) g₀ (a := p.1) (b := p.2)
      (by rw [Prod.mk.eta]; exact mem_orbit_self p)
    rwa [hg₀] at h2
  have hnex : g₀ • p.2 ≠ x := by
    intro h0
    exact hp (MulAction.injective g₀ (h0.trans hg₀.symm)).symm
  have hnbB : g₀ • p.2 ∈ B := Relation.ReflTransGen.single (Or.inl hnb)
  -- primitivity forces `B = univ`
  rcases IsPreprimitive.isTrivialBlock_of_isBlock hblock with hsub | huniv
  · exact absurd (hsub hnbB hxB) hnex
  · have hy : y ∈ B := by
      rw [huniv]
      exact Set.mem_univ y
    exact hy

end Theorem835

end FiveTransitive.OddOrder.Isaacs.Ch08

end CFSG
