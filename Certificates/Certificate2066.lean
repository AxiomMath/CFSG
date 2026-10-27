module

public import CFSG.Sporadic.FischerOddCore.Fi22CentOrderCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22Cent
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheck
import Certificates.Kernel.Sporadic.Fi22.C2066
import Certificates.Kernel.Sporadic.Fi22.E2065Eq
import Certificates.Certificate3039
import Certificates.Certificate3147

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Co2.Native in
open CFSG.Certificates.Native CFSG.Monster.B.Fischer in
theorem certificate2066 : (fi22CentOrderOK 0 = true)
    ∧ (fi22CentOrderOK 1 = true)
    ∧ (fi22CentOrderOK 2 = true)
    ∧ (fi22CentOrderOK 3 = true)
    ∧ (fi22CentOrderOK 4 = true) :=
  KernelSpor.Fi22C2066.certificate2066_of KernelSpor.Fi22CentB.text_eq

end Certificates
