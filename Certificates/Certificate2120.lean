module

public import CFSG.Sporadic.ONOddCore.LiftCheckInputs
public meta import CFSG.Sporadic.ONOddCore.LiftPayload
public meta import CFSG.Sporadic.ONOddCore.QuotOuterCheck
public meta import CFSG.Sporadic.Schreier.ONCheckAux
import Certificates.Kernel.Sporadic.OddCore.ON2120K
import Certificates.Certificate2212
import Certificates.Certificate2217
import Certificates.Certificate3171

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.ONOddCore CFSG.ONSchreier CFSG.ONSchreier.Native in
open CFSG.PSL3Four.Native CFSG.Sporadic.ON.Native in
theorem certificate2120 : candidatesCheck (wordArrs Data.MWords) = true :=
  KernelSpor.ON2120.facts2120

end Certificates
