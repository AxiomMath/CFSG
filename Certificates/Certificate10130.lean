module

public import Certificates.Data.HeSylowThree
import Certificates.Kernel.SporSch.HeThree.Facts
import CFSG.Certificates.Kernel.Misc.CentPtSound

public section

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem certificate10130 : heS3QNonabOK () = true := by
  rw [heS3QNonabOK.eq_1]
  simp only [KernelSporSch.HeThree.bindQ.1, KernelSporSch.HeThree.bindQ.2 0 (by decide),
    KernelSporSch.HeThree.bindQ.2 1 (by decide), CFSG.KC.Misc.CentPt.unpack_get!]
  decide +kernel

end Certificates
