module

public import Certificates.Data.BabyTwoBD0
import Certificates.Certificate9206
import Certificates.Certificate9111
import Certificates.Kernel.Fi23M.Keys
import Certificates.Kernel.Fi23BD0.Glue

public section

open CFSG.LocalAnalysis.GLTheoremA.H1017.BabyTwoBD0Native

namespace Certificates

open CertificateChecks

theorem certificate101708 : CFSG.LocalAnalysis.GLTheoremA.H1017.BabyTwoBD0Native.babyTwoBD0Check () = true := by
  unfold babyTwoBD0Check bD0OK
  rw [CFSG.KD.Fi23K.orbitData_eq']
  exact KernelFi23BD0.bD0_ok

end Certificates
