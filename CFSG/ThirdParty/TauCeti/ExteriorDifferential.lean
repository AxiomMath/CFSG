/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors; CFSG contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.ExteriorAlgebra
public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import TauCeti.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic.Abel

/-!
# The differential of an exterior algebra comodule

The SAME native comodule differential acts on the exterior algebra by the ordinary product
rule and sends `ι(m)` to `ι(d(m))`. These identities supply the infinitesimal determinant-line
bridge in Chevalley's theorem, without a factorial or a characteristic restriction.

The tensor-contraction multiplication argument generalizes the private `tensorComponent_mul`
in `TauCeti/Algebra/AlgebraicGroup/Tangent/InvariantDerivation.lean` at commit
`6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380`. That source is copyright (c) 2026 The Tau Ceti
contributors and distributed under Apache 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Here the left tensor factor is an arbitrary, possibly noncommutative algebra, which is needed
for the exterior algebra. The existing native coaction, differential and generator inclusion
are reused; no second Lie action is defined. Names are kept in the `CFSG.ThirdParty` namespace.

## References

* A. Borel, *Linear Algebraic Groups*, second edition (1991), Theorem 5.1.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
-/

public noncomputable section

open scoped TensorProduct
open LinearMap TauCeti

universe u v w

variable {k : Type u} [CommRing k] {H : Type v} [CommRing H] [_root_.Bialgebra k H]

namespace CFSG.ThirdParty.TauCeti

/-- Contraction by a tangent derivation satisfies the product rule against the counit. -/
theorem tensorComponent_mul_derivation {A : Type w} [Ring A] [Algebra k A]
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) (X Y : A ⊗[k] H) :
    tensorComponent ((Bialgebra.CounitAlgebra.algEquivSelf k H k).toLinearMap ∘ₗ
        d.toLinearMap) (X * Y) =
      tensorComponent ((Bialgebra.CounitAlgebra.algEquivSelf k H k).toLinearMap ∘ₗ
          d.toLinearMap) X * tensorComponent (Coalgebra.counit (R := k)) Y +
        tensorComponent (Coalgebra.counit (R := k)) X *
          tensorComponent ((Bialgebra.CounitAlgebra.algEquivSelf k H k).toLinearMap ∘ₗ
            d.toLinearMap) Y := by
  induction X using TensorProduct.inductionOn with
  | add X X' hX hX' => simp only [add_mul, map_add, hX, hX']; abel
  | tmul a h =>
    induction Y using TensorProduct.inductionOn with
    | add Y Y' hY hY' => simp only [mul_add, map_add, hY, hY']; abel
    | tmul b h' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, tensorComponent_tmul,
        LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, Derivation.coeFn_coe,
        Bialgebra.CounitAlgebra.algEquivSelf_apply_mul, Algebra.algebraMap_self,
        RingHom.id_apply, add_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [add_comm, mul_comm (Coalgebra.counit h'), mul_comm (Coalgebra.counit h)]

namespace Comodule

open _root_.TauCeti.Comodule

variable {M : Type w} [AddCommGroup M] [Module k M] [Comodule k H M]

/-- Contracting the native coaction by the counit is the identity. -/
theorem tensorComponent_counit_coact (m : M) :
    tensorComponent (Coalgebra.counit (R := k)) (coact (R := k) (C := H) m) = m := by
  rw [tensorComponent_def, LinearMap.comp_apply, lTensor_counit_coact]
  simp

attribute [local instance] exteriorAlgebra

/-- The actual native differential satisfies the product rule on the exterior algebra. -/
theorem differential_exteriorAlgebra_mul
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k))
    (x y : ExteriorAlgebra k M) :
    differential (R := k) (H := H) (M := ExteriorAlgebra k M) d (x * y) =
      differential (R := k) (H := H) (M := ExteriorAlgebra k M) d x * y +
        x * differential (R := k) (H := H) (M := ExteriorAlgebra k M) d y := by
  simp only [differential_apply, exteriorAlgebra_coact, AlgHom.toLinearMap_apply, map_mul]
  rw [tensorComponent_mul_derivation]
  have hε (z : ExteriorAlgebra k M) :
      tensorComponent (Coalgebra.counit (R := k)) (exteriorAlgebraCoact k H M z) = z := by
    rw [tensorComponent_def, LinearMap.comp_apply]
    have hz : (Coalgebra.counit (R := k)).lTensor (ExteriorAlgebra k M)
        (exteriorAlgebraCoact k H M z) = z ⊗ₜ[k] 1 := by
      simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.flip_apply,
        TensorProduct.mk_apply] using LinearMap.congr_fun
          (exteriorAlgebraCoact_counit (R := k) (H := H) (M := M)) z
    rw [hz]
    simp
  rw [hε x, hε y]

/-- The actual differential on an exterior generator is the included original differential. -/
theorem differential_exteriorAlgebra_ι
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) (m : M) :
    differential (R := k) (H := H) (M := ExteriorAlgebra k M) d (ExteriorAlgebra.ι k m) =
      ExteriorAlgebra.ι k (differential (R := k) (H := H) (M := M) d m) := by
  simpa only [Hom.exteriorAlgebraι_apply] using
    ((Hom.exteriorAlgebraι k H M).map_differential d m).symm

end Comodule

end CFSG.ThirdParty.TauCeti
