/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import CFSG.ThirdParty.TauCeti.DiagonalizableCentralizer
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace
import TauCeti.Algebra.DualNumber.Convolution

/-!
# The Lie algebra of the centralizer of a diagonalizable subgroup

This file is adapted from the TauCeti repository, file
`TauCeti/Algebra/AlgebraicGroup/DiagonalizableGroup/Centralizer/Tangent.lean` as of commit
`3c85a89bedd31a6470cac38648f51cc8310b173d` (the file is unchanged at `main` commit
`9b5ddaa11d617c84d46732ef8318190eb32842c6`), released under the Apache 2.0 license. The CFSG
dependency pin `6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380` predates it. It builds on the port of
`Centralizer/Basic.lean` in `CFSG/ThirdParty/TauCeti/DiagonalizableCentralizer.lean`, and its
declarations are placed in the same namespace `CFSG.ThirdParty.TauCeti.BialgHom`.

Let `G = Spec H` be an affine group scheme over a commutative ring `R` and `D(X) → G` a closed
diagonalizable subgroup with coordinate map `π : H →ₐc[R] R[X]`. The centralizer `Z_G(D(X))` is
the closed subgroup scheme cut out by `centralizerHopfIdeal π`. This file identifies its Lie
algebra inside the Lie algebra of `G`: it is the subspace fixed by the adjoint action of `D(X)`,
that is, the weight space of the trivial character in the weight decomposition of `Lie G` under
`D(X)`.

Both sides are conditions on a tangent vector `d` at the identity of `G`, viewed as a counit-valued
derivation of `H`. The tangent vector lies in the Lie algebra of the centralizer when it kills the
coefficients of the conjugation defects; evaluating a derivation on the conjugation defect is
differentiating the conjugating variable, and this yields the convolution commutator of `d` with
the universal point of `D(X)`. The adjoint action of the universal point of `D(X)` on `d`, which
differentiates the conjugated variable, is the convolution conjugate `π ⋆ d ⋆ π⁻¹`. Both
conditions therefore say that `d` and `π` commute in the convolution algebra. The convolution
commutator is computed on dual-number points, as the infinitesimal coefficient of the conjugate of
`π` by the tangent point of `d`.

The hypotheses are those needed to speak of the adjoint representation on the single module
`Lie G = Module.Dual R (Bialgebra.CotangentSpace R H)`: the augmentation cotangent space of `H`
is finite projective. No smoothness, reducedness or field hypothesis enters.

## Main declarations

* `cotangentLinearEquiv_mem_lieSubalgebra_centralizerHopfIdeal_iff`: **a tangent vector lies in
  the Lie algebra of the centralizer of `D(X)` exactly when it has trivial weight under `D(X)`.**
* `lieSubalgebra_centralizerHopfIdeal_toSubmodule`: the Lie algebra of the centralizer is the
  trivial weight space, transported along cotangent duality.
* `mem_adjointWeightSpace_iff_adDerivation`: weight-space membership tested on the universal point
  of `D(X)`, for `R`, `H` and `X` in independent universes.

## Adaptations to the pinned API

* **Universes.** Upstream takes `R`, `H` and `X` in one universe, because its proof starts from
  `Derivation.mem_adjointWeightSpace_iff_universalPointAction`, whose universal point of `D(X)` is
  an object of `CommAlgCat` in the universe of `H`. Here `R : Type u`, `H : Type v` and
  `X : Type w` are independent, as in the port of `Centralizer/Basic.lean`. That criterion and
  `Derivation.tangentScalarExtensionEquiv_adjointAction` are replaced by the new
  `mem_adjointWeightSpace_iff_adDerivation`. Its proof pushes the pinned
  `Derivation.tangentScalarExtensionEquiv_adjointComodule_endOfPoint`, at the universal point of
  `G` over `ULift H`, forward to an arbitrary value algebra: the point action of a comodule
  (`TauCeti.Comodule.rTensor_comp_endOfPoint`), tangent scalar extension
  (`Derivation.mapValue_tangentScalarExtensionEquiv`) and the adjoint action
  (`Derivation.mapValue_adDerivation`) are natural in the value algebra. Accordingly the
  coefficient algebra `CommAlgCat.of R R[X]` of upstream is `R[X]` itself. The tori
  `D(Multiplicative (Fin r →₀ ℤ))` of `CFSG.LieType.AlgebraicGroups.TorusCentralizerScheme` need
  this: their character group lives in `Type`, their Hopf algebra in an arbitrary universe.
* `Derivation.tangentScalarExtensionEquiv_tmul` and `Bialgebra.CounitAlgebra.algEquivSelf_map`,
  which the pin does not have, are replaced by the private `tangentScalarExtensionEquiv_one_tmul`
  and by a direct computation in `algEquivSelf_mapValue_ofId_apply`.
* `TensorProduct.map_algebraTensorProduct_map` is the ported `map_algebraTensorProduct_map`.
* The section `Smaller` (the centralizer of `D(Y) → D(X) → G` for `q : X →* Y`) relies on
  `Derivation.adjointWeightSpace_mapDomainBialgHom_comp`, which the pin does not have, and is not
  ported.

## Conventions

The first tensor factor of `TauCeti.HopfAlgebra.conjugationAlgHom` is the conjugating variable: it
is `i₁ * i₂ * i₁⁻¹`, Milne's `Ad(g)(x) = g x g⁻¹`. The conjugation defect `centralizerDefect` keeps
`G` in that factor and puts `D(X)` in the conjugated one, and
`TauCeti.HopfAlgebra.pointConjugationAlgHom g` specializes the same first factor to a rational
point `g`. Lie-algebra membership differentiates the conjugating variable; the weight condition is
the adjoint action `Ad(π) d = π ⋆ d ⋆ π⁻¹` of the universal point of `D(X)`
(`Derivation.adDerivation`), which differentiates the conjugated variable.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a (the Lie algebra of a closed subgroup) and §13
  (tori acting on schemes).
* SGA 3, Exposé XI, Corollaire 5.3.
-/

public section

open TensorProduct TrivSqZeroExt WithConv

namespace CFSG.ThirdParty.TauCeti.BialgHom

open _root_.TauCeti

universe u v w x

variable {R : Type u} {H : Type v} {X : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X]

/-- Conjugating a point by the dual-number tangent point of a tangent vector: the infinitesimal
coefficient of the conjugate is the convolution commutator of the tangent vector with the point.
This mirrors `Derivation.snd_conjugate_tangentPoint`, which conjugates the tangent point by the
point instead. -/
private theorem snd_tangentPoint_conjugate {B : Type*} [CommRing B] [Algebra R B]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B))
    (g : WithConv (H →ₐ[R] Bialgebra.CounitAlgebra R H B)) (a : H) :
    snd (((derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).val *
        AlgHom.mapValue (H := H) (inlAlgHom R (Bialgebra.CounitAlgebra R H B)
          (Bialgebra.CounitAlgebra R H B)) g *
        (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).val⁻¹).ofConv a) =
      (toConv (↑d : H →ₗ[R] Bialgebra.CounitAlgebra R H B) * toConv g.ofConv.toLinearMap -
        toConv g.ofConv.toLinearMap *
          toConv (↑d : H →ₗ[R] Bialgebra.CounitAlgebra R H B)).ofConv a := by
  let q := AlgHom.mapValue (H := H) (inlAlgHom R (Bialgebra.CounitAlgebra R H B)
    (Bialgebra.CounitAlgebra R H B)) g
  let p := (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).val
  let F := (fstHom R (Bialgebra.CounitAlgebra R H B) (Bialgebra.CounitAlgebra R H B)).toLinearMap
  let S := (sndHom (Bialgebra.CounitAlgebra R H B)
    (Bialgebra.CounitAlgebra R H B)).restrictScalars R
  let D := toConv (↑d : H →ₗ[R] Bialgebra.CounitAlgebra R H B)
  let G := toConv g.ofConv.toLinearMap
  have hqF : F ∘ₗ q.ofConv.toLinearMap = g.ofConv.toLinearMap := by
    ext x
    simp [F, q, AlgHom.mapValue_apply]
  have hqS : S ∘ₗ q.ofConv.toLinearMap = 0 := by
    ext x
    simp [S, q, AlgHom.mapValue_apply]
  have hpF : F ∘ₗ p.ofConv.toLinearMap = (1 : WithConv (H →ₗ[R] _)).ofConv := by
    ext x
    exact fst_apply_of_mem_tangentKer
      (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).2 x
  have hpS : S ∘ₗ p.ofConv.toLinearMap = D.ofConv := by
    ext x
    exact derivationMulEquivTangentKer_apply_snd (Multiplicative.ofAdd d) x
  have hpinv : p⁻¹ = (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd (-d))).val := by
    rw [ofAdd_neg, map_inv, Subgroup.coe_inv]
  have hpinvF : F ∘ₗ (p⁻¹).ofConv.toLinearMap = (1 : WithConv (H →ₗ[R] _)).ofConv := by
    rw [hpinv]
    ext x
    exact fst_apply_of_mem_tangentKer
      (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd (-d))).2 x
  have hpinvS : S ∘ₗ (p⁻¹).ofConv.toLinearMap = -D.ofConv := by
    rw [hpinv]
    ext x
    exact derivationMulEquivTangentKer_apply_snd (Multiplicative.ofAdd (-d)) x
  -- Negation passes through convolution; `mul_neg` does not apply because the convolution ring
  -- and the pointwise additive group of `WithConv` expose different negation instances.
  have hneg : G * -D = -(G * D) := by
    apply ofConv_injective
    ext c
    simp [(Coalgebra.Repr.arbitrary R c).convMul_apply]
  have hpqF : F ∘ₗ (p * q).ofConv.toLinearMap = g.ofConv.toLinearMap := by
    rw [← ofConv_toConv ((p * q).ofConv.toLinearMap), AlgHom.toLinearMap_convMul]
    dsimp only [F]
    rw [LinearMap.algHom_comp_convMul_distrib]
    rw [hpF, hqF]
    simp only [toConv_ofConv, one_mul, ofConv_toConv]
  have hpqS : S ∘ₗ (p * q).ofConv.toLinearMap = (D * G).ofConv := by
    rw [← ofConv_toConv ((p * q).ofConv.toLinearMap), AlgHom.toLinearMap_convMul]
    dsimp only [S]
    rw [WithConv.snd_comp_convMul]
    rw [hpF, hqS, hpS, hqF]
    simp only [toConv_ofConv, toConv_zero, mul_zero, zero_add]
    rfl
  have hc : S ∘ₗ (p * q * p⁻¹).ofConv.toLinearMap = (D * G - G * D).ofConv := by
    rw [← ofConv_toConv ((p * q * p⁻¹).ofConv.toLinearMap), AlgHom.toLinearMap_convMul]
    dsimp only [S]
    rw [WithConv.snd_comp_convMul]
    rw [hpqF, hpinvS, hpqS, hpinvF]
    simp only [toConv_ofConv, toConv_neg, mul_one]
    rw [hneg, sub_eq_add_neg, add_comm]
  have ha := LinearMap.congr_fun hc a
  simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, sndHom_apply,
    AlgHom.toLinearMap_apply, S, q, p, D, G] using ha

/-- The infinitesimal coefficient of the product map of two dual-number points, on a pure
tensor. -/
private theorem snd_productMap_tmul {C : Type*} [CommRing C] [Algebra R C]
    (f g : H →ₐ[R] DualNumber C) (a b : H) :
    snd (Algebra.TensorProduct.productMap f g (a ⊗ₜ[R] b)) =
      fst (f a) * snd (g b) + snd (f a) * fst (g b) := by
  rw [Algebra.TensorProduct.productMap_apply_tmul, snd_mul, op_smul_eq_mul, smul_eq_mul]

/-- A point pushed into the dual numbers by the constant inclusion takes constant values. -/
private theorem mapValue_inlAlgHom_ofConv_apply {C : Type*} [CommRing C] [Algebra R C]
    (g : WithConv (H →ₐ[R] C)) (h : H) :
    (AlgHom.mapValue (H := H) (inlAlgHom R C C) g).ofConv h = inl (g.ofConv h) := by
  simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply, inlAlgHom_apply]

/-- The values of a point regarded as counit-algebra-valued, through the identification of the
counit algebra with its coefficient ring. -/
private theorem pointInCounitAlgebra_ofConv_apply {B : Type*} [CommRing B] [Algebra R B]
    (g : WithConv (H →ₐ[R] B)) (h : H) :
    (Derivation.pointInCounitAlgebra B g).ofConv h =
      (Bialgebra.CounitAlgebra.algEquivSelf R H B).symm (g.ofConv h) := by
  rw [Derivation.pointInCounitAlgebra_apply]
  exact (Bialgebra.CounitAlgebra.algEquivSelf_symm_apply R H B _).symm

/-- The values of a tangent vector with extended coefficients, through the identification of the
counit algebras with their coefficient rings. -/
private theorem algEquivSelf_mapValue_ofId_apply {B : Type*} [CommRing B] [Algebra R B]
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (a : H) :
    Bialgebra.CounitAlgebra.algEquivSelf R H B (Derivation.mapValue (Algebra.ofId R B) d a) =
      algebraMap R B (Bialgebra.CounitAlgebra.algEquivSelf R H R (d a)) := by
  rw [Bialgebra.CounitAlgebra.algEquivSelf_apply, Derivation.mapValue_apply,
    Bialgebra.CounitAlgebra.algEquivSelf_apply]
  rfl

section Universal

variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]

attribute [local instance] Derivation.adjointComodule

/-- The scalar extension of a tangent vector with coefficient `1` is the tangent vector with
extended coefficients. -/
private theorem tangentScalarExtensionEquiv_one_tmul {B : Type*} [CommRing B] [Algebra R B]
    (f : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    Derivation.tangentScalarExtensionEquiv (R := R) (A := H) (B := B) (1 ⊗ₜ[R] f) =
      Derivation.mapValue (Algebra.ofId R B) (Derivation.cotangentLinearEquiv (B := R) f) := by
  ext a
  rw [Derivation.tangentScalarExtensionEquiv_tmul_apply, one_mul, Derivation.mapValue_apply,
    Derivation.cotangentLinearEquiv_apply_apply, Algebra.ofId_apply]

/-- The adjoint coaction acts at an algebra-valued point in any universe as convolution
conjugation, after the scalar-extension identification of tangent vectors. The pinned
`Derivation.tangentScalarExtensionEquiv_adjointComodule_endOfPoint` states this for value algebras
in `CommAlgCat` in the universe of `R` and `H`. Every point is the image of the universal point of
`G` over `ULift H`, and the point action, tangent scalar extension and the adjoint action are all
natural in the value algebra. -/
private theorem tangentScalarExtensionEquiv_endOfPoint_one_tmul {A : Type x} [CommRing A]
    [Algebra R A] (g : H →ₐ[R] A) (y : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    Derivation.tangentScalarExtensionEquiv (R := R) (A := H) (B := A)
        (Comodule.endOfPoint (Module.Dual R (Bialgebra.CotangentSpace R H)) g (1 ⊗ₜ[R] y)) =
      Derivation.adDerivation A (Derivation.pointInCounitAlgebra A (toConv g))
        (Derivation.tangentScalarExtensionEquiv (R := R) (A := H) (B := A) (1 ⊗ₜ[R] y)) := by
  let V := Module.Dual R (Bialgebra.CotangentSpace R H)
  let e : ULift.{max u v} H ≃ₐ[R] H := ULift.algEquiv
  let A₀ : CommAlgCat.{max u v} R := CommAlgCat.of R (ULift.{max u v} H)
  let g₀ : WithConv (H →ₐ[R] A₀) := toConv e.symm.toAlgHom
  let φ : A₀ →ₐ[R] A := g.comp e.toAlgHom
  have hφ : φ.comp g₀.ofConv = g := by
    ext h
    simp [φ, g₀]
  have h1 : LinearMap.rTensor V φ.toLinearMap ((1 : A₀) ⊗ₜ[R] y) = (1 : A) ⊗ₜ[R] y := by
    rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]
  have hnat := LinearMap.congr_fun (Comodule.rTensor_comp_endOfPoint V φ g₀.ofConv)
    ((1 : A₀) ⊗ₜ[R] y)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply, hφ,
    h1] at hnat
  have hp : AlgHom.mapValue (H := H)
      (Bialgebra.CounitAlgebra.mapAlgHom (R := R) (A := H) (B := A₀) (C := A) φ)
        (Derivation.pointInCounitAlgebra A₀ g₀) =
      Derivation.pointInCounitAlgebra A (toConv g) := by
    apply WithConv.ofConv_injective
    ext h
    rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
      Bialgebra.CounitAlgebra.mapAlgHom_apply, Derivation.pointInCounitAlgebra_apply,
      Derivation.pointInCounitAlgebra_apply, ← hφ]
    rfl
  rw [← hnat, ← Derivation.mapValue_tangentScalarExtensionEquiv φ,
    Derivation.tangentScalarExtensionEquiv_adjointComodule_endOfPoint A₀ g₀,
    Derivation.mapValue_adDerivation, hp, Derivation.mapValue_tangentScalarExtensionEquiv, h1]

/-- **Weight-space membership on the universal point of `D(X)`, in any universes.** A tangent
vector `y` has weight `α` under `D(X)` exactly when the adjoint action of the universal point of
`D(X)`, with values in `R[X]`, multiplies its scalar extension by the basis element `[α]`. This is
the pinned `Derivation.mem_adjointWeightSpace_iff_universalPointAction`, transported along
`Derivation.tangentScalarExtensionEquiv_adjointAction`, without its restriction to a common
universe of `R`, `H` and `X`. -/
theorem mem_adjointWeightSpace_iff_adDerivation (π : H →ₐc[R] MonoidAlgebra R X) (α : X)
    (y : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    y ∈ Derivation.adjointWeightSpace π α ↔
      Derivation.adDerivation (MonoidAlgebra R X)
          (Derivation.pointInCounitAlgebra (MonoidAlgebra R X) (toConv π.toAlgHom))
          (Derivation.tangentScalarExtensionEquiv (R := R) (A := H) (B := MonoidAlgebra R X)
            (1 ⊗ₜ[R] y)) =
        Derivation.tangentScalarExtensionEquiv (R := R) (A := H) (B := MonoidAlgebra R X)
          (MonoidAlgebra.single α (1 : R) ⊗ₜ[R] y) := by
  rw [← tangentScalarExtensionEquiv_endOfPoint_one_tmul,
    (Derivation.tangentScalarExtensionEquiv (R := R) (A := H)
      (B := MonoidAlgebra R X)).injective.eq_iff, Derivation.mem_adjointWeightSpace]
  have h := DiagonalizableGroup.endOfPoint_tmul_comp
    (Module.Dual R (Bialgebra.CotangentSpace R H)) π (AlgHom.id R (MonoidAlgebra R X)) 1 y
  rw [AlgHom.id_comp, one_smul, AlgHom.toLinearMap_id, LinearMap.lTensor_id,
    LinearMap.id_apply] at h
  rw [h, ← TensorProduct.comm_tmul R _ _ y (MonoidAlgebra.single α (1 : R)),
    (TensorProduct.comm R _ _).injective.eq_iff]

end Universal

variable (π : H →ₐc[R] MonoidAlgebra R X)

/-- Evaluating a tangent vector of `G` on the conjugation of a coordinate, in the conjugating
variable, with the universal point of `D(X)` in the conjugated variable, computes the convolution
commutator of the tangent vector with that point. -/
private theorem lid_map_conjugationAlgHom (d : Derivation R H (Bialgebra.CounitAlgebra R H R))
    (h : H) :
    TensorProduct.lid R (MonoidAlgebra R X)
        (TensorProduct.map ((Bialgebra.CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ
            (d : H →ₗ[R] Bialgebra.CounitAlgebra R H R)) π.toAlgHom.toLinearMap
          (HopfAlgebra.conjugationAlgHom (R := R) (H := H) h)) =
      Bialgebra.CounitAlgebra.algEquivSelf R H (MonoidAlgebra R X)
        ((toConv (↑(Derivation.mapValue (Algebra.ofId R (MonoidAlgebra R X)) d) :
              H →ₗ[R] Bialgebra.CounitAlgebra R H (MonoidAlgebra R X)) *
            toConv (Derivation.pointInCounitAlgebra (MonoidAlgebra R X)
              (toConv π.toAlgHom)).ofConv.toLinearMap -
          toConv (Derivation.pointInCounitAlgebra (MonoidAlgebra R X)
              (toConv π.toAlgHom)).ofConv.toLinearMap *
            toConv (↑(Derivation.mapValue (Algebra.ofId R (MonoidAlgebra R X)) d) :
              H →ₗ[R] Bialgebra.CounitAlgebra R H (MonoidAlgebra R X))).ofConv
          h) := by
  let A := MonoidAlgebra R X
  let d' := Derivation.mapValue (Algebra.ofId R A) d
  let p := Derivation.pointInCounitAlgebra A (toConv π.toAlgHom)
  let T := (derivationMulEquivTangentKer R H A (Multiplicative.ofAdd d')).val
  let Q := AlgHom.mapValue (H := H)
    (inlAlgHom R (Bialgebra.CounitAlgebra R H A) (Bialgebra.CounitAlgebra R H A)) p
  have hconj := AlgHom.congr_fun
    (HopfAlgebra.productMap_comp_conjugationAlgHom (R := R) (H := H) T Q) h
  rw [AlgHom.comp_apply] at hconj
  rw [← snd_tangentPoint_conjugate d' p h, ← hconj]
  have hmaps : (TensorProduct.lid R (MonoidAlgebra R X)).toLinearMap ∘ₗ
      TensorProduct.map ((Bialgebra.CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ
        (d : H →ₗ[R] Bialgebra.CounitAlgebra R H R)) π.toAlgHom.toLinearMap =
      (Bialgebra.CounitAlgebra.algEquivSelf R H A).toLinearMap ∘ₗ
        (sndHom (Bialgebra.CounitAlgebra R H A) (Bialgebra.CounitAlgebra R H A)).restrictScalars R
          ∘ₗ (Algebra.TensorProduct.productMap T.ofConv Q.ofConv).toLinearMap := by
    apply TensorProduct.ext'
    intro a b
    have hT : snd (T.ofConv a) = d' a :=
      derivationMulEquivTangentKer_apply_snd (Multiplicative.ofAdd d') a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul,
      TensorProduct.lid_tmul, AlgEquiv.toLinearMap_apply, Derivation.coeFn_coe,
      AlgHom.toLinearMap_apply, LinearMap.restrictScalars_apply, sndHom_apply,
      snd_productMap_tmul, Q, mapValue_inlAlgHom_ofConv_apply, fst_inl, snd_inl, mul_zero,
      zero_add, hT, map_mul, d', algEquivSelf_mapValue_ofId_apply, p,
      pointInCounitAlgebra_ofConv_apply, AlgEquiv.apply_symm_apply, BialgHom.coe_toAlgHom,
      Algebra.smul_def]
    rfl
  exact LinearMap.congr_fun hmaps _

variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]

/-- **The Lie algebra of the centralizer of a diagonalizable subgroup is the fixed part of the
adjoint action of that subgroup.** A tangent vector of `G` at the identity, viewed as a
counit-valued derivation through `Derivation.cotangentLinearEquiv`, lies in the Lie algebra of
`Z_G(D(X))` exactly when it has trivial weight under `D(X)`. -/
theorem cotangentLinearEquiv_mem_lieSubalgebra_centralizerHopfIdeal_iff
    (x : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    Derivation.cotangentLinearEquiv (B := R) x ∈
        (centralizerHopfIdeal π).lieSubalgebra (B := R) ↔
      x ∈ Derivation.adjointWeightSpace π 1 := by
  -- Weight-space membership becomes invariance under the adjoint action of the universal point,
  -- and Lie-algebra membership becomes vanishing on the generators of the centralizer ideal.
  rw [mem_adjointWeightSpace_iff_adDerivation, tangentScalarExtensionEquiv_one_tmul,
    ← MonoidAlgebra.one_def, tangentScalarExtensionEquiv_one_tmul,
    HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span _ (centralizerHopfIdeal_toIdeal π)]
  simp only [Set.forall_mem_range, Prod.forall]
  set d := Derivation.cotangentLinearEquiv (B := R) x
  set A := MonoidAlgebra R X
  set d' := Derivation.mapValue (Algebra.ofId R A) d
  set p := Derivation.pointInCounitAlgebra A (toConv π.toAlgHom)
  set D : WithConv (H →ₗ[R] Bialgebra.CounitAlgebra R H A) :=
    toConv (↑d' : H →ₗ[R] Bialgebra.CounitAlgebra R H A)
  set P : WithConv (H →ₗ[R] Bialgebra.CounitAlgebra R H A) := toConv p.ofConv.toLinearMap
  set P' : WithConv (H →ₗ[R] Bialgebra.CounitAlgebra R H A) :=
    toConv (p⁻¹).ofConv.toLinearMap
  -- Killing the coefficients of the conjugation defect is vanishing of the commutator of `d`
  -- with the universal point of `D(X)`.
  have hgen (h : H) :
      (∀ χ, d (centralizerCoefficient π h χ) = 0) ↔ (D * P - P * D).ofConv h = 0 := by
    have hcoeff : (∀ χ, d (centralizerCoefficient π h χ) = 0) ↔
        TensorProduct.map ((Bialgebra.CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ
            (d : H →ₗ[R] Bialgebra.CounitAlgebra R H R)) LinearMap.id
          (centralizerDefect π h) = 0 := by
      rw [map_centralizerDefect_eq_zero_iff]
      simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, Derivation.coeFn_coe,
        EmbeddingLike.map_eq_zero_iff]
    rw [hcoeff, ← (TensorProduct.lid R (MonoidAlgebra R X)).map_eq_zero_iff,
      centralizerDefect_def, map_sub, map_sub, map_algebraTensorProduct_map,
      AlgHom.toLinearMap_id, LinearMap.comp_id, LinearMap.id_comp, lid_map_conjugationAlgHom,
      TensorProduct.map_tmul]
    simp only [LinearMap.comp_apply, Derivation.coeFn_coe, Derivation.map_one_eq_zero, map_zero,
      TensorProduct.zero_tmul, sub_zero, EmbeddingLike.map_eq_zero_iff, D, P, d', p, A]
  rw [forall_congr' hgen]
  have hPP' : P * P' = 1 := by
    rw [← AlgHom.toLinearMap_convMul, mul_inv_cancel, AlgHom.toLinearMap_convOne]
  have hP'P : P' * P = 1 := by
    rw [← AlgHom.toLinearMap_convMul, inv_mul_cancel, AlgHom.toLinearMap_convOne]
  -- The adjoint action of the universal point is convolution conjugation.
  have had : Derivation.adDerivation A p d' = d' ↔ P * D * P' = D := by
    constructor
    · intro he
      rw [← Derivation.toConv_coe_adDerivation, he]
    · intro he
      ext a
      rw [Derivation.adDerivation_apply]
      exact DFunLike.congr_fun (congrArg ofConv he) a
  rw [had]
  constructor
  · intro hcomm
    have hDP : D * P = P * D := by
      rw [← sub_eq_zero]
      apply ofConv_injective
      rw [ofConv_zero]
      exact LinearMap.ext hcomm
    rw [← hDP, mul_assoc, hPP', mul_one]
  · intro he h
    have hPD : P * D = D * P := by
      calc P * D = P * D * P' * P := by rw [mul_assoc (P * D), hP'P, mul_one]
        _ = D * P := by rw [he]
    rw [hPD, sub_self, ofConv_zero, LinearMap.zero_apply]

/-- The Lie algebra of the centralizer of a diagonalizable subgroup is the trivial weight space of
the adjoint action of that subgroup, transported along cotangent duality. -/
theorem lieSubalgebra_centralizerHopfIdeal_toSubmodule :
    ((centralizerHopfIdeal π).lieSubalgebra (B := R)).toSubmodule =
      (Derivation.adjointWeightSpace π 1).map
        (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R) :
          Module.Dual R (Bialgebra.CotangentSpace R H) →ₗ[R]
            Derivation R H (Bialgebra.CounitAlgebra R H R)) := by
  ext d
  rw [LieSubalgebra.mem_toSubmodule, Submodule.mem_map_equiv,
    ← cotangentLinearEquiv_mem_lieSubalgebra_centralizerHopfIdeal_iff,
    LinearEquiv.apply_symm_apply]

end CFSG.ThirdParty.TauCeti.BialgHom
