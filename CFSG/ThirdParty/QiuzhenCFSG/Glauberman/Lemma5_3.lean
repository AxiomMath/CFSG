module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Data.Nat.Prime.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Glauberman, Lemma 5.3 ([6], §5; `refs/glauberman-p-stable.tex` L1460–L1475)

Let `P` be a normal subgroup of a finite `p`-group `S`, and let `A` be the automorphism
group of `S`.  Then `C_A(P) ∩ C_A(S/P)` — the automorphisms of `S` that fix `P` pointwise
and induce the identity on the quotient `S ⧸ P` — is a `p`-group.

## Proof (paper L1462–L1472)

Let `a` lie in the intersection and put `n = |P|`.  For `g ∈ S` write `g^a = g·h(g)` with
`h(g) ∈ P` (this is where the identity-on-`S/P` condition is used: `a` maps every coset to
itself).  Since `a` fixes `P` pointwise, `h(g)^a = h(g)`, so by induction on `k`
`g^(aᵏ) = g·h(g)ᵏ`; in particular `g^(aⁿ) = g·h(g)ⁿ = g` because `h(g) ∈ P` and the order
of `h(g)` divides `n = |P|`.  Hence `aⁿ = 1`.  Since `P` is a subgroup of the finite
`p`-group `S`, `n = |P|` divides `|S| = pᵐ`, so `n` is a power of `p`; therefore every
element of the intersection has `p`-power order, i.e. the intersection is a `p`-group.

The paper uses this lemma in the proof of Lemma 6.3 for the group
`C_N(K)/(C_N(K) ∩ D)`; the statement is kept general here (any finite `p`-group `S`).

Note on the shape of condition (ii): instead of building the induced automorphism
homomorphism `C_A(P) →* MulAut (S ⧸ P)` and taking its kernel, the identity-on-`S/P`
condition is expressed directly on representatives: `a` maps every coset to itself
(`QuotientGroup.mk' P (a x) = QuotientGroup.mk' P x`), which is exactly what the proof
needs (`h(g) ∈ P` in the paper's notation) and keeps the definition usable.
-/

namespace CFSG.Glauberman

variable {S : Type*} [Group S]

/-- The pointwise centralizer `C_A(P)` of a subgroup `P ≤ S` in the automorphism group
`A = MulAut S` of `S` ([6], Lemma 5.3): the automorphisms of `S` fixing every element of
`P`. -/
@[expose]
public def pointwiseCentralizer (P : Subgroup S) : Subgroup (MulAut S) where
  carrier := {a : MulAut S | ∀ x : S, x ∈ P → a x = x}
  one_mem' := by
    intro x hx
    simp
  mul_mem' := by
    intro a b ha hb x hx
    simp [ha x hx, hb x hx]
  inv_mem' := by
    intro a ha x hx
    have h1 : a (a⁻¹ x) = x := by
      simp
    exact a.injective (h1.trans (ha x hx).symm)

/-- Membership in `pointwiseCentralizer P`: `a` fixes every element of `P`. -/
@[simp]
public theorem mem_pointwiseCentralizer {P : Subgroup S} {a : MulAut S} :
    a ∈ pointwiseCentralizer P ↔ ∀ x : S, x ∈ P → a x = x := by
  rfl

/-- The intersection `C_A(P) ∩ C_A(S/P)` of [6], Lemma 5.3: the automorphisms `a` of `S`
that fix the normal subgroup `P` pointwise and induce the identity on the quotient
`S ⧸ P` (expressed on representatives: every coset of `P` is mapped to itself). -/
@[expose]
public def lemma5_3Centralizer (P : Subgroup S) [P.Normal] : Subgroup (MulAut S) where
  carrier := {a : MulAut S | (∀ x : S, x ∈ P → a x = x) ∧
      ∀ x : S, QuotientGroup.mk' P (a x) = QuotientGroup.mk' P x}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · intro x hx
      simp
    · intro x
      simp
  mul_mem' := by
    intro a b ha hb
    refine ⟨?_, ?_⟩
    · intro x hx
      simp [ha.1 x hx, hb.1 x hx]
    · intro x
      simpa using (ha.2 (b x)).trans (hb.2 x)
  inv_mem' := by
    intro a ha
    refine ⟨?_, ?_⟩
    · intro x hx
      have h1 : a (a⁻¹ x) = x := by
        simp
      exact a.injective (h1.trans (ha.1 x hx).symm)
    · intro x
      -- `a` maps the coset of `a⁻¹ x` to itself; by `a (a⁻¹ x) = x` this is the coset of `x`
      have h := ha.2 (a⁻¹ x)
      have h1 : a (a⁻¹ x) = x := by
        simp
      simpa [h1] using h.symm

/-- Membership in `lemma5_3Centralizer P`: fixing `P` pointwise and mapping every coset of
`P` to itself. -/
@[simp]
public theorem mem_lemma5_3Centralizer {P : Subgroup S} [P.Normal] {a : MulAut S} :
    a ∈ lemma5_3Centralizer P ↔ (∀ x : S, x ∈ P → a x = x) ∧
      ∀ x : S, QuotientGroup.mk' P (a x) = QuotientGroup.mk' P x := by
  rfl

/-- An element `a` of `lemma5_3Centralizer P` satisfies `a ^ |P| = 1`.  This is the
computation of the paper's proof (L1464–L1471): writing `g^a = g·h(g)` with `h(g) ∈ P`
(the coset condition), induction on `k` gives `g^(aᵏ) = g·h(g)ᵏ` (using that `a`, hence
every power of `a`, fixes `P` pointwise), and `h(g)^|P| = 1` since `h(g) ∈ P` and
`|P| = n`. -/
private theorem pow_card_eq_one_of_mem {P : Subgroup S} [P.Normal] {a : MulAut S}
    (ha : a ∈ lemma5_3Centralizer P) : a ^ Nat.card P = 1 := by
  have haP : ∀ x : S, x ∈ P → a x = x := ha.1
  have haq : ∀ x : S, QuotientGroup.mk' P (a x) = QuotientGroup.mk' P x := ha.2
  have hak : ∀ k : ℕ, a ^ k ∈ lemma5_3Centralizer P := fun k => pow_mem ha k
  apply MulEquiv.ext
  intro g
  -- h(g) = g⁻¹ * a g lies in P, so that a g = g * h(g)
  have hmem : g⁻¹ * a g ∈ P := by
    have hq : QuotientGroup.mk' P (a g) = QuotientGroup.mk' P g := haq g
    have h1 : (a g)⁻¹ * g ∈ P := QuotientGroup.eq.mp hq
    -- (g⁻¹ * a g)⁻¹ = (a g)⁻¹ * g
    have h2 : (g⁻¹ * a g)⁻¹ ∈ P := by simpa [mul_inv_rev] using h1
    exact (inv_mem_iff.mp h2)
  let hg : S := g⁻¹ * a g
  have hhg : hg ∈ P := by simpa [hg] using hmem
  have hga : a g = g * hg := by
    change a g = g * (g⁻¹ * a g)
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  -- induction on k: (a ^ k) g = g * hg ^ k
  have hmain : ∀ k : ℕ, (a ^ k) g = g * hg ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          (a ^ (k + 1)) g = (a ^ k * a) g := by rw [pow_succ]
          _ = (a ^ k) (a g) := by simp
          _ = (a ^ k) (g * hg) := by rw [hga]
          _ = (a ^ k) g * (a ^ k) hg := map_mul (a ^ k) g hg
          _ = (g * hg ^ k) * (a ^ k) hg := by rw [ih]
          _ = (g * hg ^ k) * hg := by rw [(hak k).1 hg hhg]
          _ = g * hg ^ (k + 1) := by rw [mul_assoc, ← pow_succ]
  -- hg ^ |P| = 1, since the order of hg divides |P|
  have hgn : hg ^ Nat.card P = 1 := by
    have hord : orderOf hg ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P hhg
    exact (orderOf_dvd_iff_pow_eq_one (x := hg) (n := Nat.card P)).1 hord
  -- (a ^ |P|) g = g
  simp [hmain (Nat.card P), hgn]

/-- Every element of `lemma5_3Centralizer P` is a `p`-element: since `a ^ |P| = 1` and
`|P|` divides `|S| = pᵐ`, the order of `a` divides `pᵐ` and is therefore a power of `p`. -/
private theorem pElement_of_mem {p : ℕ} [Fact p.Prime] [Finite S] (hS : IsPGroup p S)
    {P : Subgroup S} [P.Normal] {a : MulAut S} (ha : a ∈ lemma5_3Centralizer P) :
    ∃ k : ℕ, a ^ p ^ k = 1 := by
  have han : a ^ Nat.card P = 1 := pow_card_eq_one_of_mem ha
  obtain ⟨m, hSm⟩ := IsPGroup.exists_card_eq hS
  have hdivS : Nat.card P ∣ Nat.card S := Subgroup.card_subgroup_dvd_card P
  have hdivp : Nat.card P ∣ p ^ m := by
    rwa [hSm] at hdivS
  have hord : orderOf a ∣ Nat.card P := (orderOf_dvd_iff_pow_eq_one (x := a)).2 han
  have hordp : orderOf a ∣ p ^ m := dvd_trans hord hdivp
  obtain ⟨k, _hk_le, hk⟩ := (Nat.dvd_prime_pow (p := p) (m := m) (i := orderOf a)
    (Fact.out : p.Prime)).1 hordp
  refine ⟨k, ?_⟩
  exact (orderOf_dvd_iff_pow_eq_one (x := a) (n := p ^ k)).1 (hk.symm ▸ dvd_rfl)

/-- [6], Lemma 5.3 (`refs/glauberman-p-stable.tex` L1460–L1475): let `P` be a normal
subgroup of a finite `p`-group `S`, and let `A` be the automorphism group of `S`.  Then
`C_A(P) ∩ C_A(S/P)` — the automorphisms fixing `P` pointwise and inducing the identity on
`S ⧸ P` — is a `p`-group. -/
public theorem lemma5_3 {p : ℕ} [Fact p.Prime] [Finite S] (hS : IsPGroup p S)
    (P : Subgroup S) [P.Normal] : IsPGroup p (↥(lemma5_3Centralizer P)) := by
  intro a
  obtain ⟨k, hk⟩ := pElement_of_mem (p := p) hS a.2
  refine ⟨k, ?_⟩
  apply Subtype.ext
  simpa using hk

end CFSG.Glauberman
