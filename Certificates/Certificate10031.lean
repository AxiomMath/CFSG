module

public import CFSG.Monster.GMS.Fi23FusionCertInputs
import Certificates.Kernel.Fi23R.Fact10031

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi23.Native in
theorem certificate10031 :
    huntCertificate = true := by
  unfold CFSG.Sporadic.Fi23.Native.huntCertificate
  rw [CFSG.KD.Fi23K.orbitData_eq']
  exact KernelFi23R.hunt_ok

end Certificates
