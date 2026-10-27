/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Cotangent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Smooth.Containment
public import TauCeti.Algebra.AlgebraicGroup.Smooth.IdentityComponent

/-!
# Smooth closed subgroups with the full Lie algebra

This file is adapted from the TauCeti repository at `main` commit
`6fee5c0a9fb3444eb4aa6a4a6248c33258a11d5c`. It ports the identity-component Lie-algebra
computation and the closed-subgroup equality theorem added after the current CFSG dependency pin
`6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380`, together with the derivation lemma they rest on.
The declarations are reproduced in the `CFSG.ThirdParty.TauCeti` namespace with unchanged
statements, so that a later TauCeti bump does not clash with the upstream names.

Let `G` be a smooth connected affine group of finite type over an algebraically closed field,
and `H ≤ G` a smooth closed subgroup with `Lie(H) = Lie(G)`. Then `H = G`.

The subgroup `H` need not be connected, so the comparison of smooth connected closed subgroups
by their Lie algebras does not apply to it directly. Its identity component `H°` is smooth and
connected, and has the same Lie algebra as `H`: a tangent vector at the identity kills every
idempotent, in particular the one cutting out `H°`. The coordinate map `O(G) → O(H°)` is then
surjective with surjective differential, so it is injective.

The source files and their main declarations are:

* `TauCeti/RingTheory/Derivation/Idempotent.lean`:
  `CFSG.ThirdParty.TauCeti.Derivation.apply_eq_zero_of_isIdempotentElem`: a derivation kills
  every idempotent;
* `TauCeti/Algebra/AlgebraicGroup/HopfIdeal/Smooth/LieAlgebra.lean`:
  `CFSG.ThirdParty.TauCeti.HopfIdeal.lieSubalgebra_identityComponentHopfIdeal_eq_top`: the
  identity component has the same Lie algebra as the group, and
  `CFSG.ThirdParty.TauCeti.HopfIdeal.eq_bot_of_lieSubalgebra_eq_top`: a smooth closed subgroup
  of a smooth connected group with the full Lie algebra is the whole group.

All remaining declarations used by the proofs already exist at the CFSG pin and are reused
rather than redeclared, in particular the pinned `TauCeti.derivationCompLieHom`,
`TauCeti.derivationCompLieHom_comp`, `TauCeti.derivationCompLieHom_apply`,
`TauCeti.HopfIdeal.quotientLieHom_apply`, `TauCeti.HopfIdeal.quotientLieEquiv_apply_coe`,
`TauCeti.HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span`,
`TauCeti.HopfIdeal.ker_eq_bot_of_smooth_of_connected_of_conormalSubspace_eq_bot` and
`TauCeti.HopfIdeal.conormalSubspace_ker_eq_bot_of_surjective_of_derivationCompLieHom_surjective`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 10.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.

## Adaptations

* every ported declaration is placed in a namespace rooted at `CFSG.ThirdParty.TauCeti`, and
  references to ported declarations are correspondingly qualified;
* the upstream import `TauCeti.RingTheory.Derivation.Idempotent` does not exist at the pin, so
  its content is ported below on top of `Mathlib.RingTheory.Derivation.Basic`; the upstream
  imports of `TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Cotangent`,
  `TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Smooth.Containment` and
  `TauCeti.Algebra.AlgebraicGroup.Smooth.IdentityComponent` are kept at their pinned versions;
* references to declarations that already exist at the pin are qualified with `TauCeti` and are
  not redeclared.
-/

public section

namespace CFSG.ThirdParty.TauCeti

universe u

namespace Derivation

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCancelCommMonoid M] [Module A M] [Module R M]

/-- A derivation vanishes on every idempotent. -/
@[simp]
theorem apply_eq_zero_of_isIdempotentElem (D : _root_.Derivation R A M) {e : A}
    (he : IsIdempotentElem e) : D e = 0 := by
  have hD : D e = e • D e + e • D e := by
    simpa only [he.eq] using D.leibniz e e
  have hsmul : e • D e = 0 := by
    have h := congrArg (e • ·) hD
    simp only [smul_add, smul_smul, he.eq] at h
    exact left_eq_add.mp h
  simpa only [hsmul, add_zero] using hD

end Derivation

namespace HopfIdeal

variable {k : Type u} [Field k] [IsAlgClosed k] {H : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The identity component of a finite-type affine group over an algebraically closed field has
the same Lie algebra as the group. -/
theorem lieSubalgebra_identityComponentHopfIdeal_eq_top :
    (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).lieSubalgebra
      (B := k) = ⊤ := by
  let _ : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  let e : H := PrimeSpectrum.connectedComponentIdempotent (R := H)
    (TauCeti.Bialgebra.augmentationPoint k H)
  have hspan : (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal =
      Ideal.span {1 - e} := by
    rw [TauCeti.HopfAlgebra.identityComponentHopfIdeal_toIdeal]
    ext x
    exact PrimeSpectrum.mem_connectedComponentIdeal_iff.trans Ideal.mem_span_singleton'.symm
  rw [eq_top_iff]
  intro d _
  rw [TauCeti.HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span _ hspan]
  rintro x rfl
  have he : IsIdempotentElem e :=
    PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent _
  rw [map_sub, d.map_one_eq_zero, Derivation.apply_eq_zero_of_isIdempotentElem d he, sub_zero]

/-- A smooth closed subgroup of a smooth connected affine group over an algebraically closed
field is the whole group as soon as its Lie algebra is the whole Lie algebra.

The order on Hopf ideals reverses inclusion of closed subgroups, so `I = ⊥` says that the closed
subgroup cut out by `I` is everything. -/
theorem eq_bot_of_lieSubalgebra_eq_top [Algebra.Smooth k H]
    [ConnectedSpace (PrimeSpectrum H)] (I : TauCeti.HopfIdeal k H)
    [Algebra.Smooth k (H ⧸ I.toIdeal)] (hI : I.lieSubalgebra (B := k) = ⊤) : I = ⊥ := by
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient H I
  let J := TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := Q)
  let _ : Algebra.Smooth k Q := ‹Algebra.Smooth k (H ⧸ I.toIdeal)›
  -- The coordinate map of the inclusion of the identity component of the subgroup.
  let f : H →ₐc[k] Q ⧸ J.toIdeal :=
    (Bialgebra.Quotient.mkBialgHom J.toIdeal).comp (Bialgebra.Quotient.mkBialgHom I.toIdeal)
  have hf : Function.Surjective f :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hdf : Function.Surjective (TauCeti.derivationCompLieHom (B := k) f) := by
    rw [TauCeti.derivationCompLieHom_comp, LieHom.coe_comp]
    -- A closed subgroup with the full Lie algebra has surjective differential.
    have hsurj (K : Type u) [CommRing K] [HopfAlgebra k K] (L : TauCeti.HopfIdeal k K)
        (hL : L.lieSubalgebra (B := k) = ⊤) :
        Function.Surjective
          (TauCeti.derivationCompLieHom (B := k)
            (Bialgebra.Quotient.mkBialgHom L.toIdeal)) :=
      fun d ↦ ⟨(TauCeti.HopfIdeal.quotientLieEquiv L).symm
          ⟨d, hL ▸ LieSubalgebra.mem_top d⟩, by
        rw [TauCeti.derivationCompLieHom_apply, ← TauCeti.HopfIdeal.quotientLieHom_apply,
          ← TauCeti.HopfIdeal.quotientLieEquiv_apply_coe, LieEquiv.apply_symm_apply]⟩
    exact (hsurj H I hI).comp (hsurj Q J lieSubalgebra_identityComponentHopfIdeal_eq_top)
  have hker := TauCeti.HopfIdeal.ker_eq_bot_of_smooth_of_connected_of_conormalSubspace_eq_bot
    f hf ((TauCeti.smoothCommHopfAlgProperty_iff _).mpr inferInstance) inferInstance
    ((TauCeti.smoothCommHopfAlgProperty_iff _).mpr
      (TauCeti.FiniteTypeCommHopfAlgCat.smooth_identityComponent Q))
    (TauCeti.FiniteTypeCommHopfAlgCat.connectedSpace_identityComponent Q)
    (TauCeti.HopfIdeal.conormalSubspace_ker_eq_bot_of_surjective_of_derivationCompLieHom_surjective
      f hf hdf)
  refine le_antisymm (fun x hx ↦ ?_) bot_le
  rw [← hker, TauCeti.HopfIdeal.mem_ker]
  have hx0 : Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal x = 0 := by
    rw [Bialgebra.Quotient.mkBialgHom_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact hx
  simp only [f, BialgHom.comp_apply, hx0, map_zero]

end HopfIdeal

end CFSG.ThirdParty.TauCeti
