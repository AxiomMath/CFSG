module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03A6Data
public meta import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03A6Data
import CFSG.Certificates.Kernel.PermCent.Gs03CSound
import Certificates.Kernel.PermCent.KG1037401

public section

open CFSG.LocalAnalysis.WeakClosure81.Gs03A6 CFSG.GH74.KGroups.A6
  CFSG.Certificates.Kernel.PkCV.Gs03

namespace Certificates

open CFSG.LocalAnalysis.WeakClosure81.Gs03A6 in
theorem certificate1037401 : a6GenCheck () = true := by
  unfold a6GenCheck
  rw [Bool.and_eq_true]
  exact ⟨gs03CoverCheck_of_C QA _ _ K1037401.kCov, gs03ClassesCheck_of_C QP _ 5 _ K1037401.kCls⟩

end Certificates
