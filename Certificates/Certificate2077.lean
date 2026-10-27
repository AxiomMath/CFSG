
module


public import CFSG.Sporadic.FischerOddCore.Fi24R2KCheckInputs
import Certificates.Kernel.Sporadic.Fi24K.C2077

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Co2.Native in
open CFSG.Certificates.Native in
theorem certificate2077 : (fi24KChainOK fi24KStrong fi24KWords = true)
    ∧ (fi24PChainOK fi24PStrong fi24PWords = true)
    ∧ (fi24SOK fi24KStrong fi24S0 fi24STree fi24PStrong = true) := KernelSpor.Fi24C.certificate2077

end Certificates
