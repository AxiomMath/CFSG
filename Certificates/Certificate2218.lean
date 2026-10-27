module

public import CFSG.Sporadic.Schreier.PairHSCertInputs
import Certificates.Kernel.SporSch.Pair.HSCert

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Certificates.Native in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native in
theorem certificate2218 : hsCertOK = true := KernelSporSch.PHSCert.facts

end Certificates
