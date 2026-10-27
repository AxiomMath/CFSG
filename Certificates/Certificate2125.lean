module

public import CFSG.Sporadic.ONOddCore.NonextCheckInputs
public meta import CFSG.Sporadic.ONOddCore.NonextPayload
public meta import CFSG.Sporadic.ONOddCore.LiftHomCheck
public meta import CFSG.Sporadic.Schreier.ONCheckR3E
import Certificates.Kernel.Sporadic.OddCore.ON2125
import Certificates.Certificate2212
import Certificates.Certificate2217
import Certificates.Certificate3171

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.ONOddCore CFSG.ONSchreier CFSG.ONSchreier.Native in
open CFSG.Sporadic.ON.Native in
theorem certificate2125 : nonextOK (wordArrs Data.MWords) flatLifts nonextCert nonextWords = true :=
  KernelSpor.ON2125.facts2125

end Certificates
