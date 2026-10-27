module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03U33Data
public meta import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03U33Data
import CFSG.Certificates.Kernel.PermCent.Gs03CSound
import Certificates.Kernel.PermCent.KG1037402

public section

open CFSG.LocalAnalysis.WeakClosure81.Gs03U33 CFSG.GH74.KGroups.U33
  CFSG.Certificates.Kernel.PkCV.Gs03

namespace Certificates

open CFSG.LocalAnalysis.WeakClosure81.Gs03U33 in
theorem certificate1037402 : u33GenCheck () = true := by
  unfold u33GenCheck
  rw [Bool.and_eq_true]
  exact ⟨decide_map_cOf _ _ K1037402.kReps, gs03ClassesCheck_of_C QP _ 4 _ K1037402.kCls⟩

end Certificates
