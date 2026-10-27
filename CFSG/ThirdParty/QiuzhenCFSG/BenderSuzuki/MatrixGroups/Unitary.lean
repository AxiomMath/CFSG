module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

namespace CFSG
end CFSG
open CFSG

/-!
# Projective unitary matrix group interfaces

This file contains the current matrix-level unitary models used by the
Peterfalvi Part II formalization.  They are deliberately low-level interfaces:
recognition and Chapter IV transport statements live in the PF chapter files.
-/

namespace CFSG.BenderSuzuki
namespace MatrixGroups

universe w

/--
A nondegenerate Hermitian form on the standard `n`-dimensional matrix space.
The stored involution is the field involution, and `form_hermitian` records
the Hermitian symmetry `J_{ij} = conj J_{ji}`.
-/
public structure HermitianForm (n : ℕ) (F : Type w) [Field F] where
  conj : F ≃+* F
  conj_involutive : Function.Involutive conj
  form : Matrix (Fin n) (Fin n) F
  form_hermitian : ∀ i j, conj (form j i) = form i j
  form_nondegenerate : form.det ≠ 0


/-- Conjugate transpose with respect to the field involution stored in a Hermitian form. -/
@[expose] public def HermitianForm.conjTranspose {n : ℕ} {F : Type w} [Field F]
    (J : HermitianForm n F) (A : Matrix (Fin n) (Fin n) F) :
    Matrix (Fin n) (Fin n) F :=
  fun i j => J.conj (A j i)

/-- The exact unitary group preserving the Hermitian form `J`. -/
@[expose] public def HermitianForm.unitarySubgroup {n : ℕ} {F : Type w} [Field F]
    (J : HermitianForm n F) : Subgroup (GL (Fin n) F) := by
  let adjoint (A : Matrix (Fin n) (Fin n) F) := J.conjTranspose A
  have adjoint_mul (A B : Matrix (Fin n) (Fin n) F) :
      adjoint (A * B) = adjoint B * adjoint A := by
    ext i j
    simp only [adjoint, HermitianForm.conjTranspose, Matrix.mul_apply,
      map_sum, map_mul]
    apply Finset.sum_bij (fun k _ => k) <;> simp [mul_comm]
  have adjoint_one : adjoint 1 = 1 := by
    classical
    ext i j
    by_cases h : i = j
    · subst j
      simp [adjoint, HermitianForm.conjTranspose]
    · have hji : j ≠ i := fun hji => h hji.symm
      simp [adjoint, HermitianForm.conjTranspose, h, hji]
  refine
    { carrier := {A | adjoint (A : Matrix (Fin n) (Fin n) F) * J.form *
          (A : Matrix (Fin n) (Fin n) F) = J.form}
      one_mem' := by
        change adjoint (1 : Matrix (Fin n) (Fin n) F) * J.form * 1 = J.form
        rw [adjoint_one]
        simp
      mul_mem' := ?_
      inv_mem' := ?_ }
  · intro A B hA hB
    change adjoint ((A * B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        J.form * ((A * B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = J.form
    calc
      adjoint ((A * B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          J.form * ((A * B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        (adjoint (B : Matrix (Fin n) (Fin n) F) *
          adjoint (A : Matrix (Fin n) (Fin n) F)) * J.form *
          ((A : Matrix (Fin n) (Fin n) F) *
            (B : Matrix (Fin n) (Fin n) F)) := by
        change adjoint ((A : Matrix (Fin n) (Fin n) F) *
            (B : Matrix (Fin n) (Fin n) F)) * J.form *
          ((A : Matrix (Fin n) (Fin n) F) *
            (B : Matrix (Fin n) (Fin n) F)) = _
        rw [adjoint_mul]
      _ = adjoint (B : Matrix (Fin n) (Fin n) F) *
          (adjoint (A : Matrix (Fin n) (Fin n) F) * J.form *
            (A : Matrix (Fin n) (Fin n) F)) *
          (B : Matrix (Fin n) (Fin n) F) := by simp only [mul_assoc]
      _ = adjoint (B : Matrix (Fin n) (Fin n) F) * J.form *
          (B : Matrix (Fin n) (Fin n) F) := by rw [hA]
      _ = J.form := hB
  · intro A hA
    change adjoint ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        J.form * ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = J.form
    calc
      adjoint ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          J.form * ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        adjoint ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (adjoint (A : Matrix (Fin n) (Fin n) F) * J.form *
            (A : Matrix (Fin n) (Fin n) F)) *
          ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by rw [hA]
      _ = (adjoint ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            adjoint (A : Matrix (Fin n) (Fin n) F)) * J.form *
          ((A : Matrix (Fin n) (Fin n) F) *
            ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
        simp only [mul_assoc]
      _ = adjoint ((A : Matrix (Fin n) (Fin n) F) *
            ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * J.form *
          ((A : Matrix (Fin n) (Fin n) F) *
            ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
        rw [adjoint_mul]
      _ = J.form := by
        have hmul :
            (A : Matrix (Fin n) (Fin n) F) *
                ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
          simp
        rw [hmul, adjoint_one]
        simp

/-- Membership in the unitary subgroup, exposed without unfolding the subgroup
construction downstream. -/
@[simp] public theorem HermitianForm.mem_unitarySubgroup_iff
    {n : ℕ} {F : Type w} [Field F] (J : HermitianForm n F)
    (A : GL (Fin n) F) :
    A ∈ J.unitarySubgroup ↔
      J.conjTranspose (A : Matrix (Fin n) (Fin n) F) * J.form *
        (A : Matrix (Fin n) (Fin n) F) = J.form :=
  Iff.rfl

/-- The special unitary group: exact unitary isometries with determinant one. -/
@[expose] public def HermitianForm.specialSubgroup {n : ℕ} {F : Type w} [Field F]
    (J : HermitianForm n F) : Subgroup (GL (Fin n) F) :=
  J.unitarySubgroup ⊓ Matrix.GeneralLinearGroup.det.ker

/-- Membership in the special unitary subgroup as the unitary equation and
determinant-one equation. -/
@[simp] public theorem HermitianForm.mem_specialSubgroup_iff
    {n : ℕ} {F : Type w} [Field F] (J : HermitianForm n F)
    (A : GL (Fin n) F) :
    A ∈ J.specialSubgroup ↔
      J.conjTranspose (A : Matrix (Fin n) (Fin n) F) * J.form *
          (A : Matrix (Fin n) (Fin n) F) = J.form ∧
        Matrix.GeneralLinearGroup.det A = 1 := by
  change (A ∈ J.unitarySubgroup ∧
    Matrix.GeneralLinearGroup.det A = 1) ↔ _
  rw [J.mem_unitarySubgroup_iff]

/-- A special unitary matrix is unitary. -/
public theorem HermitianForm.specialSubgroup_le_unitarySubgroup
    {n : ℕ} {F : Type w} [Field F] (J : HermitianForm n F) :
    J.specialSubgroup ≤ J.unitarySubgroup :=
  inf_le_left


/-- The projective special unitary group, as the image of `SU(J)` in `PGL`. -/
public abbrev ProjectiveSpecialUnitaryMatrixGroup
    {n : ℕ} {F : Type w} [Field F] (J : HermitianForm n F) :=
  J.specialSubgroup.map Matrix.ProjGenLinGroup.mk

end MatrixGroups
end CFSG.BenderSuzuki
