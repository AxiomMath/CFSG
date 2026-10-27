
module


public import Certificates.Data.CFSGNative.Fi22.Inv
import Certificates.Kernel.Fi22Inv.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi22.Native

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native in
theorem certificate1007 : invCertificate 3 = true := by
  unfold invCertificate
  rw [KernelFi22C.orbitData_eq]
  exact KernelFi22I.inv_ok

end Certificates
