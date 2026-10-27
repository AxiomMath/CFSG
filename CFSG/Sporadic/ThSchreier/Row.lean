
module

public import CFSG.Sporadic.ThSchreier.RowBase

public import CFSG.Sporadic.Th.BaseBase1
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Sporadic.ThSchreier.Text
public meta import Certificates.Data.CFSGNative.Th.Base
public import CFSG.Sporadic.ThSchreier.RowInputs
public import Certificates.Certificate2322
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Matrix Pointwise

noncomputable instance instMulActionRowV : MulAction J RowV where
  smul g v := toRow (Matrix.vecMul (ofRow v) (toMat g⁻¹))
  one_smul v := by
    change toRow (Matrix.vecMul (ofRow v) (toMat (1 : J)⁻¹)) = v
    rw [inv_one, toMat_one, Matrix.vecMul_one]
    rfl
  mul_smul g h v := by
    change toRow (Matrix.vecMul (ofRow v) (toMat (g * h)⁻¹)) =
      toRow (Matrix.vecMul (ofRow (toRow (Matrix.vecMul (ofRow v) (toMat h⁻¹)))) (toMat g⁻¹))
    rw [_root_.mul_inv_rev, toMat_mul, ← Matrix.vecMul_vecMul]
    rfl

theorem rowSmul_def (g : J) (v : RowV) : g • v = toRow (Matrix.vecMul (ofRow v) (toMat g⁻¹)) :=
  rfl

theorem rowSmul_add (g : J) (u v : RowV) : g • (u + v) = g • u + g • v := by
  rw [rowSmul_def, rowSmul_def, rowSmul_def]
  exact Matrix.add_vecMul _ _ _

theorem rowSmul_zero (g : J) : g • (0 : RowV) = 0 := by
  rw [rowSmul_def]
  exact Matrix.zero_vecMul _

theorem rowPlane_imageKey {R : Array V4} {g : J} (hR : IsRows R g⁻¹) (k : Key) :
    rowPlane (imageKey (frTable R) k) = g • rowPlane k := by
  unfold imageKey
  rw [rowPlane_canon, frApply_frTable_vecMul, frApply_frTable_vecMul, hR.eq, ← Set.image_smul]
  simp only [rowPlane, Set.image_insert_eq, Set.image_singleton]
  rw [rowSmul_zero, rowSmul_add]
  rfl

private theorem native_formInv :
    eqRows (mulRows fcRows formInvRows) idRows = true ∧
      eqRows (mulRows formInvRows fcRows) idRows = true :=
  Certificates.certificate2322

theorem formF_mul_inv : formF * formFInv = 1 := by
  have h := rowsMatrix_eq_of_eqRows native_formInv.1
  rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at h

theorem formFInv_mul : formFInv * formF = 1 := by
  have h := rowsMatrix_eq_of_eqRows native_formInv.2
  rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at h

theorem psi_injective : Function.Injective psi := by
  intro u v h
  have h' : formFInv *ᵥ (formF *ᵥ u) = formFInv *ᵥ (formF *ᵥ v) := congrArg (formFInv *ᵥ ·) h
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, formFInv_mul, Matrix.one_mulVec,
    Matrix.one_mulVec] at h'

theorem psi_surjective : Function.Surjective psi := by
  intro w
  refine ⟨formFInv *ᵥ ofRow w, ?_⟩
  simp only [psi, Matrix.mulVec_mulVec, formF_mul_inv, Matrix.one_mulVec]
  rfl

@[expose] noncomputable def psiEquiv : V ≃ RowV :=
  Equiv.ofBijective psi ⟨psi_injective, psi_surjective⟩

theorem psi_smul (g : J) (u : V) : psi (toMat g *ᵥ u) = g • psi u := by
  have hinv := form_invariant (g⁻¹ : J) (g⁻¹ : J).2
  have hG : toMat g⁻¹ * toMat g = 1 := by rw [← toMat_mul, inv_mul_cancel, toMat_one]
  have key : formF * toMat g = (toMat g⁻¹)ᵀ * formF := by
    calc formF * toMat g = ((toMat g⁻¹)ᵀ * formF * toMat g⁻¹) * toMat g := by
          rw [show (toMat g⁻¹)ᵀ * formF * toMat g⁻¹ = formF from hinv]
      _ = (toMat g⁻¹)ᵀ * formF := by rw [Matrix.mul_assoc, hG, Matrix.mul_one]
  rw [rowSmul_def, psi, psi]
  simp only [ofRow_toRow]
  rw [Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose]

theorem psi_image_smul (g : J) (S : Set V) : psi '' (g • S) = g • (psi '' S) := by
  rw [smul_set_eq_image, Set.image_image, ← Set.image_smul, Set.image_image]
  exact Set.image_congr fun u _ => psi_smul g u

end CFSG.Sporadic.ThSchreier
