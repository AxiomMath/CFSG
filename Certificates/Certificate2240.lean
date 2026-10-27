
module

public import Certificates.Certificate2240Base

public import CFSG.Sporadic.Schreier.PairMcLCertInputs
import Certificates.Kernel.SporSch.Pair.McLCert

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Certificates.Native in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native in
theorem certificate2240 : mclCertOK = true := KernelSporSch.PMcLCert.facts

end Certificates
