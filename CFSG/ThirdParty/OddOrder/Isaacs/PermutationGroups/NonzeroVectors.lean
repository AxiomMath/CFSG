/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# Isaacs, Finite Group Theory — Ch. 8: transitivity on nonzero vectors

Formalizes **Isaacs Cor 8.4** (pp. 226–227): the general linear group of an
`n`-dimensional vector space over the field of order `2` acts doubly
transitively on the set of nonzero vectors.

We prove it in the natural generality that makes the argument work: over any
division ring `K` whose unit group is trivial (`Subsingleton Kˣ`, i.e. `K ≃ 𝔽₂`
for fields), the map `D ↦ D.rep` is an equivariant bijection from the
projective space `ℙ K V` onto the nonzero vectors of `V`, so *any* degree of
multiple transitivity transfers between the two actions
(`isMultiplyPretransitive_nonzero_iff_projectivization`).  Combining with
mathlib's 2-pretransitivity of `GL(V)`/`SL(V)`/`V ≃ₗ[K] V` on `ℙ K V`
(`Mathlib.LinearAlgebra.Projectivization.Action`) yields Cor 8.4 for each of
the three standard incarnations of the linear group.

Isaacs's `GL(n,2) = SL(n,2)` remark is reflected here by providing both the
`GeneralLinearGroup` and `SpecialLinearGroup` instances.

The `SubMulAction` of a group on the nonzero vectors (generalizing mathlib's
`Units.nonZeroSubMul` from `Rˣ` to an arbitrary group acting distributively)
is general-purpose and written mathlib-compatibly for future upstreaming.
-/

public section

namespace CFSG

namespace FiveTransitive.OddOrder.Isaacs.Ch08

open scoped LinearAlgebra.Projectivization

open MulAction Projectivization

/-! ### The action of a group on the nonzero vectors

A group acting distributively on an additive monoid preserves the set of
nonzero elements (mathlib has this only for `Rˣ`, as `Units.nonZeroSubMul`). -/

section NonzeroSubMulAction

variable (G V : Type*) [Group G] [AddMonoid V] [DistribMulAction G V]

/-- The nonzero elements of `V` are invariant under the action of a group `G`
acting distributively on `V`.  Generalizes `Units.nonZeroSubMul` (which is the
special case `G = Rˣ`). -/
@[expose] def nonzeroSubMulAction : SubMulAction G V where
  carrier := {v | v ≠ 0}
  smul_mem' g _ hv := (smul_ne_zero_iff_ne g).2 hv

instance instMulActionNonzero : MulAction G {v : V // v ≠ 0} :=
  inferInstanceAs <| MulAction G (nonzeroSubMulAction G V)

variable {G V}

@[simp]
lemma nonzero_smul_coe (g : G) (v : {v : V // v ≠ 0}) : (g • v : {v : V // v ≠ 0}).1 = g • v.1 :=
  rfl

end NonzeroSubMulAction

/-! ### Projective space over a field with trivial unit group

Over `𝔽₂` (more generally, whenever `Kˣ` is trivial) every line contains a
unique nonzero vector, so `ℙ K V` is equivariantly bijective with the nonzero
vectors of `V`. -/

section TrivialUnits

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- Over a division ring with trivial unit group, `Projectivization.rep` is a
one-sided inverse of `Projectivization.mk` on the nose (not just up to a
scalar). -/
lemma rep_mk_of_subsingleton_units [Subsingleton Kˣ] (v : V) (hv : v ≠ 0) :
    (Projectivization.mk K v hv).rep = v := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep K v hv
  rw [← ha, Subsingleton.elim a 1, one_smul]

variable (G : Type*) [Group G] [DistribMulAction G V] [SMulCommClass G K V]

variable (K V) in
/-- Over a division ring with trivial unit group, taking representatives is a
`G`-equivariant map from the projective space to the nonzero vectors, for any
group `G` acting `K`-linearly on `V`.  (It is bijective:
`projectivizationToNonzero_bijective`.) -/
@[expose] noncomputable def projectivizationToNonzero [Subsingleton Kˣ] :
    ℙ K V →ₑ[MonoidHom.id G] {v : V // v ≠ 0} where
  toFun D := ⟨D.rep, D.rep_nonzero⟩
  map_smul' g D := by
    ext
    change (g • D).rep = g • D.rep
    conv_lhs => rw [← D.mk_rep]
    rw [Projectivization.smul_mk]
    exact rep_mk_of_subsingleton_units _ _

lemma projectivizationToNonzero_bijective [Subsingleton Kˣ] :
    Function.Bijective (projectivizationToNonzero K V G) := by
  constructor
  · intro D E h
    have h' : D.rep = E.rep := congrArg Subtype.val h
    rw [← D.mk_rep, ← E.mk_rep]
    exact Projectivization.mk_eq_mk_iff' K _ _ _ _ |>.2 ⟨1, by rw [one_smul, h']⟩
  · intro v
    exact ⟨Projectivization.mk K v.1 v.2,
      Subtype.ext (rep_mk_of_subsingleton_units v.1 v.2)⟩

/-- Over a division ring with trivial unit group (i.e. `𝔽₂`), an action of a
group `G` by `K`-linear maps on `V` is `n`-transitive on the nonzero vectors
of `V` iff it is `n`-transitive on the projective space `ℙ K V`. -/
theorem isMultiplyPretransitive_nonzero_iff_projectivization [Subsingleton Kˣ] (n : ℕ) :
    IsMultiplyPretransitive G {v : V // v ≠ 0} n ↔ IsMultiplyPretransitive G (ℙ K V) n :=
  (IsPretransitive.of_embedding_congr (Function.surjective_id (α := G))
    (projectivizationToNonzero_bijective G)).symm

/-! ### Isaacs Cor 8.4 -/

/-- **Isaacs Cor 8.4** — `GL(n,2)` is doubly transitive on the nonzero vectors
of an `n`-dimensional vector space over the field of order `2`.  Stated for
the linear-automorphism group `V ≃ₗ[K] V` over any division ring with trivial
unit group; no dimension hypothesis is needed (in dimension `< 2` the
statement is vacuous). -/
instance [Subsingleton Kˣ] :
    IsMultiplyPretransitive (V ≃ₗ[K] V) {v : V // v ≠ 0} 2 :=
  (isMultiplyPretransitive_nonzero_iff_projectivization (K := K) _ 2).2 inferInstance

/-- **Isaacs Cor 8.4** — `GL(n,2)` is doubly transitive on the nonzero vectors
of an `n`-dimensional vector space over the field of order `2` (general linear
group form). -/
instance [Subsingleton Kˣ] :
    IsMultiplyPretransitive (LinearMap.GeneralLinearGroup K V) {v : V // v ≠ 0} 2 :=
  (isMultiplyPretransitive_nonzero_iff_projectivization (K := K) _ 2).2 inferInstance

/-- **Isaacs Cor 8.4**, special linear form — over `𝔽₂` one has
`GL(n,2) = SL(n,2)` (Isaacs's proof remark), so the special linear group is
also doubly transitive on nonzero vectors. -/
instance {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Subsingleton Kˣ] :
    IsMultiplyPretransitive (SpecialLinearGroup K V) {v : V // v ≠ 0} 2 :=
  (isMultiplyPretransitive_nonzero_iff_projectivization (K := K) _ 2).2 inferInstance

end TrivialUnits

end FiveTransitive.OddOrder.Isaacs.Ch08

end CFSG
