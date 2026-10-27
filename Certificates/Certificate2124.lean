module

public import CFSG.Sporadic.ONOddCore.MinusCheckInputs
public meta import CFSG.Sporadic.Schreier.ONCheckChain
import Certificates.Kernel.Sporadic.ON.Minus2124

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.ONOddCore CFSG.ONSchreier CFSG.ONSchreier.Native in
open CFSG.Sporadic.ON.Native in
theorem certificate2124 : minusOK qonStrongArrs CFSG.ONSchreier.Data.baseList.toArray sigmaArr = true := KernelSpor.ON.facts

end Certificates
