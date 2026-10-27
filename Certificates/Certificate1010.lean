module

public import Certificates.Data.CFSGNative.Fi22.Nfp
import Certificates.Kernel.Fi22Nfp.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi22.Native

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native in
theorem certificate1010 : nfpCertificate 3 = true := by
  unfold nfpCertificate
  rw [KernelFi22C.orbitData_eq]
  exact KernelFi22N.nfp_ok

end Certificates
