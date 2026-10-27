module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoPlaneData
import CFSG.Certificates.Kernel.D4PlaneSound
import Certificates.Kernel.D4Plane.Checks

public section

namespace Certificates

open CFSG.KC.D4PlaneP CFSG.KD.D4Plane

open CFSG.AGLEmbedding.D4Two in
theorem certificate29700 : d4PlaneCheck = true := by
  have hC : coverP es CFSG.AGLEmbedding.D4Two.d4PlaneCerts = true := by
    rw [coverP, beq_iff_eq.1 omOK, beq_iff_eq.1 psOK]
    exact coverOK
  refine d4PlaneCheck_of (ls := ls) (fun i hi => ?_) enumOK hC planesOK
  exact beq_iff_eq.1 (List.all_eq_true.1 lettersOK i (List.mem_range.2 hi))

end Certificates
