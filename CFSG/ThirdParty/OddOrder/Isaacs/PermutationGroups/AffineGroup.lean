/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.NonzeroVectors
public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.RegularNormal

/-!
# Isaacs, Finite Group Theory — Ch. 8: the affine group of `𝔽₂ⁿ` (Cor 8.7)

Formalizes **Isaacs Cor 8.7** (p. 228): for `V` an elementary abelian
`2`-group of order `2^n` (equivalently, an `n`-dimensional vector space over
the field of order `2`), the affine group `V ⋊ GL(n,2)` is a `3`-transitive
permutation group of degree `2^n`.

We state this over any division ring `K` with trivial unit group (i.e. `𝔽₂`;
see `NonzeroVectors.lean`), for the semidirect product
`Multiplicative V ⋊ GL(V)` acting on the cosets of `GL(V)`:

* `affineGroup_isMultiplyPretransitive` — the action is `3`-transitive
  (via Cor 8.4 + Cor 8.6);
* `affineGroup_quotient_faithfulSMul` — the action is faithful, so the
  affine group is a *permutation group*;
* `affineGroup_natCard_quotient` — the degree is `|V|`
  (`= 2^n = |K| ^ (dim V)`, using `natCard_eq_two_of_subsingleton_units`).

Since mathlib's `SemidirectProduct` is multiplicative, the elementary
abelian group `V` enters as `Multiplicative V`; the general transfer
instances (`SMul`/`MulAction`/`MulDistribMulAction`/`FaithfulSMul` of a group
on `Multiplicative V` induced from the additive action on `V`) are
general-purpose, mathlib-gap infrastructure.
-/

public section

namespace CFSG

namespace FiveTransitive.OddOrder.Isaacs.Ch08

open MulAction

/-! ### Actions on `Multiplicative V` -/

section MultiplicativeInstances

variable {G V : Type*}

instance [SMul G V] : SMul G (Multiplicative V) where
  smul g v := .ofAdd (g • v.toAdd)

@[simp]
lemma smul_multiplicative_toAdd [SMul G V] (g : G) (v : Multiplicative V) :
    (g • v).toAdd = g • v.toAdd :=
  rfl

@[simp]
lemma smul_multiplicative_ofAdd [SMul G V] (g : G) (v : V) :
    g • Multiplicative.ofAdd v = Multiplicative.ofAdd (g • v) :=
  rfl

instance [Monoid G] [AddMonoid V] [DistribMulAction G V] :
    MulAction G (Multiplicative V) where
  one_smul v := (congrArg Multiplicative.ofAdd (one_smul G v.toAdd)).trans
    (ofAdd_toAdd v)
  mul_smul g g' v := congrArg Multiplicative.ofAdd (mul_smul g g' v.toAdd)

/-- An additive action of `G` on `V` by additive maps is a multiplicative
action on `Multiplicative V` by multiplicative maps. -/
instance [Monoid G] [AddMonoid V] [DistribMulAction G V] :
    MulDistribMulAction G (Multiplicative V) where
  smul_mul g v w := congrArg Multiplicative.ofAdd (smul_add g v.toAdd w.toAdd)
  smul_one g := congrArg Multiplicative.ofAdd (smul_zero g)

instance [Monoid G] [AddMonoid V] [DistribMulAction G V] [FaithfulSMul G V] :
    FaithfulSMul G (Multiplicative V) where
  eq_of_smul_eq_smul h :=
    FaithfulSMul.eq_of_smul_eq_smul fun v =>
      congrArg Multiplicative.toAdd (h (Multiplicative.ofAdd v))

end MultiplicativeInstances

/-! ### Transferring multiple transitivity from nonzero vectors to
nonidentity elements -/

section NonzeroToNonidentity

variable (G : Type*) {V : Type*} [Group G] [AddGroup V] [DistribMulAction G V]

variable (V) in
/-- The equivariant bijection from the nonzero vectors of `V` onto the
nonidentity elements of `Multiplicative V`. -/
@[expose] def nonzeroToNonidentityMultiplicative :
    {v : V // v ≠ 0} →ₑ[MonoidHom.id G] {h : Multiplicative V // h ≠ 1} where
  toFun v := ⟨Multiplicative.ofAdd v.1, by
    simpa [← ofAdd_zero] using v.2⟩
  map_smul' g v := rfl

lemma nonzeroToNonidentityMultiplicative_bijective :
    Function.Bijective (nonzeroToNonidentityMultiplicative G V) := by
  constructor
  · intro v w h
    exact Subtype.ext (congrArg (fun x : {h : Multiplicative V // h ≠ 1} => x.1.toAdd) h)
  · intro h
    exact ⟨⟨h.1.toAdd, by
      simpa [← ofAdd_zero] using h.2⟩, Subtype.ext rfl⟩

/-- `n`-transitivity on the nonidentity elements of `Multiplicative V` is the
same as `n`-transitivity on the nonzero vectors of `V`. -/
theorem isMultiplyPretransitive_nonidentity_multiplicative_iff (n : ℕ) :
    IsMultiplyPretransitive G {h : Multiplicative V // h ≠ 1} n ↔
      IsMultiplyPretransitive G {v : V // v ≠ 0} n :=
  (IsPretransitive.of_embedding_congr (Function.surjective_id (α := G))
    (nonzeroToNonidentityMultiplicative_bijective (V := V) G)).symm

end NonzeroToNonidentity

/-! ### Isaacs Cor 8.7 -/

section AffineGroup

variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
  [Subsingleton Kˣ]

local notation "GL" => LinearMap.GeneralLinearGroup K V

local notation "Aff" =>
  Multiplicative V ⋊[MulDistribMulAction.toMulAut
    (LinearMap.GeneralLinearGroup K V) (Multiplicative V)]
    LinearMap.GeneralLinearGroup K V

/-- **Isaacs Cor 8.7**, transitivity clause — for `V` a vector space over the
field of order `2` (any division ring with trivial unit group), the affine
group `V ⋊ GL(V)` acts `3`-transitively on the cosets of `GL(V)`. -/
theorem affineGroup_isMultiplyPretransitive :
    IsMultiplyPretransitive Aff
      (Aff ⧸ (SemidirectProduct.inr : GL →* Aff).range) 3 := by
  have h2 : IsMultiplyPretransitive GL {h : Multiplicative V // h ≠ 1} 2 :=
    (isMultiplyPretransitive_nonidentity_multiplicative_iff (V := V) GL 2).mpr
      (inferInstanceAs (IsMultiplyPretransitive GL {v : V // v ≠ 0} 2))
  exact semidirectProduct_isMultiplyPretransitive_quotient_inrRange
    GL (Multiplicative V) h2

omit [Subsingleton Kˣ] in
/-- **Isaacs Cor 8.7**, faithfulness clause — the coset action of the affine
group is faithful, so `V ⋊ GL(V)` is a `3`-transitive *permutation group*. -/
theorem affineGroup_quotient_faithfulSMul :
    FaithfulSMul Aff (Aff ⧸ (SemidirectProduct.inr : GL →* Aff).range) :=
  semidirectProduct_quotient_inrRange_faithfulSMul GL (Multiplicative V)

omit [Subsingleton Kˣ] in
/-- **Isaacs Cor 8.7**, degree clause — the coset action of the affine group
has degree `|V|` (`= 2^n` for `V` of dimension `n` over `𝔽₂`). -/
theorem affineGroup_natCard_quotient :
    Nat.card (Aff ⧸ (SemidirectProduct.inr : GL →* Aff).range) = Nat.card V :=
  (semidirectProduct_natCard_quotient_inrRange GL (Multiplicative V)).trans
    (Nat.card_congr Multiplicative.toAdd)

end AffineGroup

/-- A division ring with trivial unit group is the field of order `2`:
its only elements are `0` and `1`.  (Complements the degree clause of
Cor 8.7: `|V| = |K| ^ dim V = 2 ^ n`.) -/
lemma natCard_eq_two_of_subsingleton_units (K : Type*) [DivisionRing K]
    [Subsingleton Kˣ] : Nat.card K = 2 := by
  have h : ∀ z : K, z = 0 ∨ z = 1 := by
    intro z
    rcases eq_or_ne z 0 with hz | hz
    · exact Or.inl hz
    · right
      obtain ⟨u, rfl⟩ := (isUnit_iff_ne_zero (a := z)).mpr hz
      rw [Subsingleton.elim u 1, Units.val_one]
  rw [Nat.card_eq_two_iff]
  refine ⟨0, 1, zero_ne_one, ?_⟩
  ext z
  simpa using h z

end FiveTransitive.OddOrder.Isaacs.Ch08

end CFSG
