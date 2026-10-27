module

public import CFSG.GH74.KGroups.L27Inputs
import CFSG.Certificates.Kernel.PermCent.CVSound
import Certificates.Kernel.PermCent.KL27
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.L27T

namespace Certificates

private theorem sub2331_eq : (elemsT L27.QP).all (fun x => L27.QA.sift x 0) = subC := by
  unfold subC
  rw [elemsT_eq_elemsC]
  simp only [List.all_map, Function.comp_def, sift_ev]

private theorem norm2331_eq : (elemsT L27.QA).all
    (fun y => (elemsT L27.QP).all fun x => L27.QP.sift (y * x * y⁻¹) 0) = normC := by
  unfold normC
  rw [elemsT_eq_elemsC, elemsT_eq_elemsC]
  simp only [List.all_map, Function.comp_def, ev_mul', ev_inv', sift_ev]

private theorem inv2331_eq : (elemsT L27.QP).all (fun x => !(decide (x * x = 1)) || decide (x = 1) ||
    (elemsT L27.QA).all fun y => !(decide (y * x = x * y)) || decide (y ^ 16 = 1)) = invC := by
  unfold invC
  rw [elemsT_eq_elemsC, elemsT_eq_elemsC]
  simp only [List.all_map, Function.comp_def, ev_mul', ev_pow', one_eq_ev, decide_ev_eq]

open CFSG Subgroup CFSG.GH74.KGroups Equiv in
theorem certificate2331 : (
 (elemsT L27.QP).all (fun x => L27.QA.sift x 0) = true 
)
    ∧ (
 (elemsT L27.QA).all
    (fun y => (elemsT L27.QP).all fun x => L27.QP.sift (y * x * y⁻¹) 0) = true 
)
    ∧ (
 (elemsT L27.QP).all (fun x => !(decide (x * x = 1)) || decide (x = 1) ||
    (elemsT L27.QA).all fun y => !(decide (y * x = x * y)) || decide (y ^ 16 = 1)) = true 
)
    ∧ (
 ∀ x y : Perm (Fin 5), Perm.sign x = 1 → x * x = 1 → x ≠ 1 →
    y * x = x * y → y ^ 16 = 1 
) := by
  refine ⟨?_, ?_, ?_, kA5Inv⟩
  · rw [sub2331_eq]
    exact kSub
  · rw [norm2331_eq]
    exact kNorm
  · rw [inv2331_eq]
    exact kInv

end Certificates
