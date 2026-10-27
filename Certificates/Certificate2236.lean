
module

public import Certificates.Certificate2236Base

public import CFSG.Sporadic.Schreier.PairJ3CertInputs
import Certificates.Kernel.SporSch.PairJ3.Cert2236

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Certificates.Native in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native in
theorem certificate2236 : j3CertOK = true :=
  KernelSporSch.PJ3Cert.certOK

end Certificates
