module

public import Certificates.Data.Kernel.Fi22.CentChecks
import Certificates.Kernel.Fi22Cent.Final
import Certificates.Kernel.Fi22Core.OrbData

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi22.Native

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native in
theorem certificate1004 : centChecksK (CFSG.Sporadic.Fi22.Native.orbitData ()) = true := by
  rw [KernelFi22C.orbitData_eq]
  exact KernelFi22Cent.cent_ok

end Certificates
