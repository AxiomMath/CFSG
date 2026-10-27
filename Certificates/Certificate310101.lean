module

public import Certificates.Data.CFSGNative.J1Sylow.Certificate
import Certificates.Kernel.J1Syl.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.J1.Sylow.Native in
theorem certificate310101 : j1SylowCertificate () = true := by
  unfold CFSG.Sporadic.J1.Sylow.Native.j1SylowCertificate
  rw [KernelSpor.J1K.orb_eq.1]
  exact KernelJ1Syl.sylow_ok

end Certificates
