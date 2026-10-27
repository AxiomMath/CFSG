
module


public import CFSG.Sporadic.Schreier.PairJ2CertInputs
import Certificates.Kernel.SporSch.Pair.J2Cert

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Certificates.Native in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native in
theorem certificate2233 : j2CertOK = true := KernelSporSch.PJ2Cert.facts

end Certificates
