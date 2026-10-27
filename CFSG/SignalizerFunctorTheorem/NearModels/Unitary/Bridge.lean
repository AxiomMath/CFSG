module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData
public import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Basic
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismHermitian

public section

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix
open CFSG.BenderSuzuki.MatrixGroups CFSG.ShultStronglyClosedTI.UnitaryAutomorphism

namespace CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut

private noncomputable def psu3Form {f : ℕ} (hf : 1 ≤ f) :
    HermitianForm 3 (GaloisField 2 (2 * f)) where
  conj := RingEquiv.ofBijective (unitaryFieldData_galoisField hf).bar
    ⟨(unitaryFieldData_galoisField hf).bar.injective,
      fun c => ⟨_, (unitaryFieldData_galoisField hf).bar_bar c⟩⟩
  conj_involutive := (unitaryFieldData_galoisField hf).bar_bar
  form := antidiagGram _
  form_hermitian i j := by
    fin_cases i <;> fin_cases j <;> simp [antidiagGram]
  form_nondegenerate := by
    simp [antidiagGram, Matrix.det_fin_three]

private theorem psu3Form_specialSubgroup {f : ℕ} (hf : 1 ≤ f) :
    (psu3Form hf).specialSubgroup =
      gramSU (unitaryFieldData_galoisField hf) (antidiagGram (GaloisField 2 (2 * f))) := by
  ext A
  rw [HermitianForm.mem_specialSubgroup_iff, mem_gramSU,
    conjTranspose_eq_transpose_map (psu3Form hf) (unitaryFieldData_galoisField hf)
      (fun _ => rfl), Units.ext_iff, GeneralLinearGroup.val_det_apply, Units.val_one]
  rfl

noncomputable def psu3EquivHypPSU {f : ℕ} (hf : 1 ≤ f) :
    hypPSU (unitaryFieldData_galoisField hf) 1 1 ≃* PSU3 2 f :=
  (hypPSUEquivPSU (unitaryFieldData_galoisField hf) (J := psu3Form hf) (fun _ => rfl) rfl).trans
    (MulEquiv.subgroupCongr (by
      rw [psu3_eq_map_gramSU hf, ← psu3Form_specialSubgroup hf]))

end CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut
