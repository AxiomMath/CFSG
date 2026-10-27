module

public import CFSG.Sporadic.J4
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Certificates.Certificate10059
public meta import Certificates.Data.CFSGNative.J4.F2
public meta import Certificates.Data.CFSGNative.J4.Data
import Certificates.Data.CFSGNative.J4.F2
import Certificates.Data.CFSGNative.J4.Data
public import CFSG.Sporadic.J4Base

public section

namespace CFSG.RankThree.PartOne

open Matrix
open scoped Matrix

section Generic

variable {n : ℕ} (H : Subgroup (GL (Fin n) (ZMod 2)))

@[expose] noncomputable def rowRepGen : Representation (ZMod 2) H (Fin n → ZMod 2) where
  toFun g := Matrix.vecMulLinear
    (((g⁻¹ : H) : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))
  map_one' := by
    refine LinearMap.ext fun w => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun w => ?_
    simp only [Matrix.vecMulLinear_apply, _root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul,
      Module.End.mul_apply, Matrix.vecMul_vecMul]

theorem rowRepGen_apply (g : H) (w : Fin n → ZMod 2) :
    rowRepGen H g w = w ᵥ* (((g⁻¹ : H) : GL (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) := rfl

theorem rowRepGen_ne_one {g : H} (hg : g ≠ 1) : rowRepGen H g ≠ 1 := by
  intro h
  apply hg
  set M : Matrix (Fin n) (Fin n) (ZMod 2) :=
    (((g⁻¹ : H) : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) with hM
  have h1 : ∀ w : Fin n → ZMod 2, w ᵥ* M = w := fun w => by
    have := LinearMap.congr_fun h w
    simpa [rowRepGen_apply, hM] using this
  have h2 : M = 1 := by
    ext i j
    have := congrFun (h1 (Pi.single i 1)) j
    rw [Matrix.single_vecMul] at this
    simp only [one_smul, Pi.single_apply] at this
    rw [Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simpa using this
    · have hji : j ≠ i := fun h => hij h.symm
      simpa [hij, hji] using this
  have h3 : g⁻¹ = 1 := Subtype.ext (Units.ext (by rw [← hM, h2]; rfl))
  simpa using h3

theorem toBilin_rowRepGen_invariant {F : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hF : ∀ g ∈ H, (g : Matrix (Fin n) (Fin n) (ZMod 2)) * F *
      (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = F) (g : H) (x y : Fin n → ZMod 2) :
    Matrix.toBilin' F (rowRepGen H g x) (rowRepGen H g y) = Matrix.toBilin' F x y := by
  set M : Matrix (Fin n) (Fin n) (ZMod 2) :=
    (((g⁻¹ : H) : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) with hMdef
  have hF' : M * F * Mᵀ = F := hF (g⁻¹ : H) (g⁻¹ : H).property
  simp only [Matrix.toBilin'_apply', rowRepGen_apply, ← hMdef]
  have e1 : y ᵥ* M = Mᵀ *ᵥ y := (Matrix.mulVec_transpose M y).symm
  calc (x ᵥ* M) ⬝ᵥ (F *ᵥ (y ᵥ* M)) = x ⬝ᵥ (M *ᵥ (F *ᵥ (Mᵀ *ᵥ y))) := by
        rw [← Matrix.dotProduct_mulVec, e1]
    _ = x ⬝ᵥ ((M * F * Mᵀ) *ᵥ y) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = x ⬝ᵥ (F *ᵥ y) := by rw [hF']

end Generic

section J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native

theorem form_inverse_check :
    eqRows (mulRows formRows (invRows formRows)) idRows = true :=
  Certificates.certificate10059

theorem formF_mul_inv :
    formF * rowsMatrix (invRows formRows) = 1 := by
  have h := congrArg rowsMatrix (eqRows_iff.1 form_inverse_check)
  rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at h

theorem formF_det_ne_zero : formF.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det formF_mul_inv
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

noncomputable abbrev rowRep : Representation (ZMod 2) J (Fin 112 → ZMod 2) :=
  rowRepGen J

@[expose] noncomputable def formB : LinearMap.BilinForm (ZMod 2) (Fin 112 → ZMod 2) :=
  Matrix.toBilin' formF

theorem formB_nondegenerate : formB.Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' formF formF_det_ne_zero

theorem formB_invariant (hM : MatFacts) (g : J) (x y : Fin 112 → ZMod 2) :
    formB (rowRep g x) (rowRep g y) = formB x y :=
  toBilin_rowRepGen_invariant J (fun g hg => form_invariant hM g hg) g x y

theorem rowRep_ne_one {g : J} (hg : g ≠ 1) : rowRep g ≠ 1 := rowRepGen_ne_one J hg

end J4

end CFSG.RankThree.PartOne
