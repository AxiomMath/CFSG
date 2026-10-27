module

public import Certificates.Data.CFSGNative.Fi22.Classes
import Certificates.Kernel.Fi22Syl.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi22.Native

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native in
theorem certificate1006 : classesCertificate 3 = true := by
  unfold classesCertificate
  rw [KernelFi22C.orbitData_eq]
  exact KernelFi22S.syl_ok

end Certificates
