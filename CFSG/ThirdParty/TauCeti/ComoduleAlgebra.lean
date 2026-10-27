/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Basic

/-!
# The comodule-algebra structure needed for fixed-point smoothness

This is the class and coaction-algebra-map section of upstream
`TauCeti/Algebra/Bialgebra/ComoduleAlgebra.lean`, at commit
`67b1599ff06528519c9908527cfc5243d0d8ed24` in TauCetiProject/TauCeti.
The CFSG pin predates that file. Only the required class/coaction API is
ported; the unrelated Hopf--Galois and coinvariant sections are omitted.
All declarations use `CFSG.ThirdParty.TauCeti` to avoid a future pin conflict.
-/

public section
open scoped TensorProduct
namespace CFSG.ThirdParty.TauCeti
open _root_.TauCeti
universe u v w x
/-- A right **comodule algebra** over an `R`-bialgebra `H`: an `R`-algebra `A` with a right
`H`-comodule structure whose coaction `A → A ⊗[R] H` is multiplicative and unital, so that it is
a homomorphism of `R`-algebras. For commutative `H` and `A` it is an action of the affine monoid
scheme `Spec H` on the affine scheme `Spec A`. -/
class ComoduleAlgebra (R : Type u) (H : Type v) (A : Type w) [CommSemiring R] [Semiring H]
    [Bialgebra R H] [Semiring A] [Algebra R A] extends _root_.TauCeti.Comodule R H A where
  /-- The coaction is unital. -/
  coact_one : coact 1 = 1
  /-- The coaction is multiplicative. -/
  coact_mul (a b : A) : coact (a * b) = coact a * coact b

namespace ComoduleAlgebra

attribute [simp] coact_one coact_mul

section Semiring

variable (R : Type u) (H : Type v) (A : Type w) [CommSemiring R] [Semiring H] [Bialgebra R H]
  [Semiring A] [Algebra R A] [ComoduleAlgebra R H A]

/-- The coaction of a comodule algebra, as a homomorphism of `R`-algebras `A →ₐ[R] A ⊗[R] H`. -/
noncomputable def coactAlgHom : A →ₐ[R] A ⊗[R] H :=
  AlgHom.ofLinearMap (_root_.TauCeti.Comodule.coact (R := R) (C := H) (M := A)) coact_one coact_mul

variable {R H A} in
@[simp]
theorem coactAlgHom_apply (a : A) :
    coactAlgHom R H A a = _root_.TauCeti.Comodule.coact (R := R) (C := H) a :=
  (rfl)

@[simp]
theorem toLinearMap_coactAlgHom :
    (coactAlgHom R H A).toLinearMap = _root_.TauCeti.Comodule.coact (R := R) (C := H) (M := A) :=
  (rfl)

/-- The coaction sends a scalar `r` to `r ⊗ 1`. -/
@[simp]
theorem coact_algebraMap (r : R) :
    _root_.TauCeti.Comodule.coact (R := R) (C := H) (algebraMap R A r) = algebraMap R A r ⊗ₜ[R] 1 := by
  rw [← coactAlgHom_apply, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]


end Semiring
end ComoduleAlgebra
end CFSG.ThirdParty.TauCeti
