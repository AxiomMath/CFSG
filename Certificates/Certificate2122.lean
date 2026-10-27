module

public import CFSG.Sporadic.ONOddCore.LiftGraphInputs
import Certificates.Kernel.Sporadic.OddCore.ON2122F
public import CFSG.Sporadic.Schreier.ONCheckLocalInputs

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.ONOddCore CFSG.ONSchreier CFSG.ONSchreier.Native in
theorem certificate2122 : (liftResOK (wordArrs Data.MWords) = true)
    ∧ (localCert.records.all (fun r => r.lifts.all liftGraphOK) = true) := KernelSpor.ON2122.facts2122

end Certificates
