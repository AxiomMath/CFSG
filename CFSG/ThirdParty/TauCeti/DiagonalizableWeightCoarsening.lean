/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace

/-!
# Pushing characters forward collects weight submodules

This file is adapted from the TauCeti repository, commit
`3c85a89bedd31a6470cac38648f51cc8310b173d` (both theorems are unchanged at `main` commit
`4fdaa79110c23d1418f87f2b4236a93074040a84`), released under the Apache 2.0 license:
`TauCeti.DiagonalizableGroup.weightSpace_mapDomainBialgHom_comp` of
`TauCeti/Algebra/AlgebraicGroup/DiagonalizableGroup/Weight.lean` and
`Derivation.adjointWeightSpace_mapDomainBialgHom_comp` of
`TauCeti/Algebra/AlgebraicGroup/Tangent/RootSpace.lean`. The CFSG dependency pin
`6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380` has neither. The statements are unchanged; the
declarations are placed in the namespace `CFSG.ThirdParty.TauCeti`, so that a later TauCeti bump
does not clash with the upstream names.

For `q : X →* Y`, the `y`-weight submodule of a comodule corestricted along `R[q] ∘ π` is the sum
of the `x`-weight submodules for `π` over the characters `x` with `q x = y`. For commutative
groups this is the restriction of a representation along `D(Y) → D(X) → G`. Applied to the
adjoint comodule, the `n`-weight space of `Lie G` for `D(N) → D(M) → G` is the sum of the
`m`-weight spaces for `D(M) → G` over `q m = n`.

## Adaptations to the pinned API

Upstream reads `DiagonalizableGroup.weightSpace` and `Derivation.adjointWeightSpace`
definitionally, which works inside the files defining them. Here neither definition is unfolded:
membership is converted through `TauCeti.DiagonalizableGroup.mem_weightSpace`,
`TauCeti.Comodule.mem_weightSpace`, `TauCeti.Comodule.corestrict_coact_apply` and
`Derivation.mem_adjointWeightSpace`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12.c (diagonalizable groups and their
  representations).
-/

public section

open scoped TensorProduct

namespace CFSG.ThirdParty.TauCeti

open _root_.TauCeti

namespace DiagonalizableGroup

variable {R : Type*} [CommSemiring R]
variable {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {X : Type*}
variable (V : Type*) [AddCommMonoid V] [Module R V] [Comodule R C V]

/-- Membership in a diagonalizable weight submodule is membership in the weight submodule of the
corestricted comodule. -/
private theorem mem_weightSpace_iff_corestrict (π : C →ₗc[R] MonoidAlgebra R X) (x : X) (v : V) :
    v ∈ _root_.TauCeti.DiagonalizableGroup.weightSpace V π x ↔
      v ∈ (letI : Comodule R (MonoidAlgebra R X) V := Comodule.Corestrict (M := V) π
        Comodule.weightSpace R X V x) := by
  let : Comodule R (MonoidAlgebra R X) V := Comodule.Corestrict (M := V) π
  rw [_root_.TauCeti.DiagonalizableGroup.mem_weightSpace, Comodule.mem_weightSpace,
    Comodule.corestrict_coact_apply]

/-- **Pushing the characters forward along a monoid homomorphism collects weight submodules.** For
`q : X →* Y`, the `y`-weight submodule after corestricting along `R[q] ∘ π` is the sum of the
`x`-weight submodules for `π` over the characters `x` with `q x = y`.

For commutative groups this is the restriction of a representation along `D(Y) → D(X) → G`. -/
theorem weightSpace_mapDomainBialgHom_comp [Monoid X] {Y : Type*} [Monoid Y]
    (π : C →ₗc[R] MonoidAlgebra R X) (q : X →* Y) (y : Y) :
    _root_.TauCeti.DiagonalizableGroup.weightSpace V ((MonoidAlgebra.mapDomainBialgHom R q :
        MonoidAlgebra R X →ₗc[R] MonoidAlgebra R Y).comp π) y =
      ⨆ x ∈ q ⁻¹' {y}, _root_.TauCeti.DiagonalizableGroup.weightSpace V π x := by
  set π' := (MonoidAlgebra.mapDomainBialgHom R q :
    MonoidAlgebra R X →ₗc[R] MonoidAlgebra R Y).comp π
  -- An `x`-weight vector for `π` is a `q x`-weight vector for `π'`.
  have hle (x : X) : _root_.TauCeti.DiagonalizableGroup.weightSpace V π x ≤
      _root_.TauCeti.DiagonalizableGroup.weightSpace V π' (q x) := fun v hv ↦ by
    rw [_root_.TauCeti.DiagonalizableGroup.mem_weightSpace, ← LinearMap.lTensor_def] at hv ⊢
    -- `CoalgHom.comp_toLinearMap` is stated for the coercion to linear maps; restate it for
    -- `toLinearMap`, which is what `mem_weightSpace` produces.
    rw [show π'.toLinearMap = (MonoidAlgebra.mapDomainBialgHom R q).toLinearMap ∘ₗ π.toLinearMap
      from CoalgHom.comp_toLinearMap _ _, LinearMap.lTensor_comp_apply, hv, LinearMap.lTensor_tmul]
    exact congrArg (v ⊗ₜ[R] ·) (MonoidAlgebra.mapDomainBialgHom_single q x 1)
  refine le_antisymm (fun v hv ↦ ?_) (iSup₂_le fun x hx ↦ by
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    exact hx ▸ hle x)
  -- Decompose `v` into its weight components for `π`, then project onto the `y`-weight
  -- component for `π'`: a component of weight `x` survives exactly when `q x = y`.
  let : Comodule R (MonoidAlgebra R X) V := Comodule.Corestrict π
  let : Comodule R (MonoidAlgebra R Y) V := Comodule.Corestrict π'
  have hcomp (x : X) : Comodule.weightProj R Y V y (Comodule.weightProj R X V x v) ∈
      ⨆ x ∈ q ⁻¹' {y}, _root_.TauCeti.DiagonalizableGroup.weightSpace V π x := by
    have hx : Comodule.weightProj R X V x v ∈ Comodule.weightSpace R Y V (q x) :=
      (mem_weightSpace_iff_corestrict V π' (q x) _).mp
        (hle x ((mem_weightSpace_iff_corestrict V π x _).mpr
          (Comodule.weightProj_mem_weightSpace x v)))
    by_cases hqx : q x = y
    · rw [Comodule.weightProj_of_mem (hqx ▸ hx)]
      exact Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem hqx
        ((mem_weightSpace_iff_corestrict V π x _).mpr (Comodule.weightProj_mem_weightSpace x v)))
    · rw [Comodule.weightProj_of_mem_of_ne (Ne.symm hqx) hx]
      exact zero_mem _
  rw [← Comodule.weightProj_of_mem (R := R) (G := Y)
      ((mem_weightSpace_iff_corestrict V π' y v).mp hv),
    ← Comodule.weightDecomposition_sum (R := R) (G := X) v, Finsupp.sum, map_sum]
  exact Submodule.sum_mem _ fun x _ ↦ by
    rw [Comodule.weightDecomposition_apply]
    exact hcomp x

end DiagonalizableGroup

namespace Derivation

universe u v w

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]
variable {M : Type w} [CommGroup M]

/-- The adjoint weight submodule is the diagonalizable weight submodule of the adjoint
comodule. -/
private theorem adjointWeightSpace_eq_weightSpace (π : H →ₐc[R] MonoidAlgebra R M) (α : M) :
    letI : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
      _root_.Derivation.adjointComodule (R := R) (H := H)
    _root_.Derivation.adjointWeightSpace π α =
      _root_.TauCeti.DiagonalizableGroup.weightSpace (Module.Dual R (Bialgebra.CotangentSpace R H))
        (π : H →ₗc[R] MonoidAlgebra R M) α := by
  let : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    _root_.Derivation.adjointComodule (R := R) (H := H)
  ext x
  rw [_root_.Derivation.mem_adjointWeightSpace, _root_.TauCeti.DiagonalizableGroup.mem_weightSpace]

/-- **Pushing the characters forward along a homomorphism `q : M →* N` collects adjoint weight
spaces.** The `n`-weight space for `D(N) → D(M) → G` is the sum of the `m`-weight spaces for
`D(M) → G` over the characters `m` with `q m = n`. -/
theorem adjointWeightSpace_mapDomainBialgHom_comp {N : Type*} [CommGroup N]
    (π : H →ₐc[R] MonoidAlgebra R M) (q : M →* N) (n : N) :
    _root_.Derivation.adjointWeightSpace ((MonoidAlgebra.mapDomainBialgHom R q).comp π) n =
      ⨆ m ∈ q ⁻¹' {n}, _root_.Derivation.adjointWeightSpace π m := by
  let : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    _root_.Derivation.adjointComodule (R := R) (H := H)
  simp only [adjointWeightSpace_eq_weightSpace, BialgHom.comp_toCoalgHom]
  exact DiagonalizableGroup.weightSpace_mapDomainBialgHom_comp _
    (π : H →ₗc[R] MonoidAlgebra R M) q n

end Derivation

end CFSG.ThirdParty.TauCeti
