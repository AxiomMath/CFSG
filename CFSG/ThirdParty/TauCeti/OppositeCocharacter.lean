/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.Algebra.Polynomial.Laurent

/-!
# The opposite cocharacter

The opposite of a cocharacter `λ : 𝔾ₘ → G` is `t ↦ λ(t⁻¹)`. On coordinates it is the composite
of `λ` with the bialgebra automorphism of the Laurent polynomials inverting the variable.

This file is adapted from the TauCeti repository, file
`TauCeti/Algebra/AlgebraicGroup/Dynamic/Points.lean` at TauCeti `main` commit
`6fee5c0a9fb3444eb4aa6a4a6248c33258a11d5c`, which contains `BialgHom.oppositeCocharacter`.
Copyright (c) 2026 The Tau Ceti contributors; released under the Apache 2.0 license
(https://www.apache.org/licenses/LICENSE-2.0).

The current CFSG dependency pin (`6e0c6acab`) predates this definition. It is reproduced in the
`CFSG.ThirdParty.TauCeti` namespace so that a later TauCeti bump does not clash with the
upstream name. The definition is unchanged.
-/

public section

namespace CFSG.ThirdParty.TauCeti.BialgHom

variable {R H : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]

/-- The opposite cocharacter, obtained by precomposing the group morphism with `t ↦ t⁻¹`. -/
@[expose] noncomputable def oppositeCocharacter (l : H →ₐc[R] LaurentPolynomial R) :
    H →ₐc[R] LaurentPolynomial R :=
  (AddMonoidAlgebra.domCongrBialgEquiv R R (AddEquiv.neg ℤ)).toBialgHom.comp l

end CFSG.ThirdParty.TauCeti.BialgHom
