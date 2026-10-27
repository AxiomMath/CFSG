module

public import CFSG.Sporadic.ONOddCore.QuotOuterCheckInputs
public meta import CFSG.Sporadic.ONOddCore.LocalAutPayload
public meta import CFSG.Sporadic.ONOddCore.SigmaTriple
public meta import CFSG.Sporadic.ONOddCore.GraphDefs
public meta import CFSG.Sporadic.Schreier.ONCheckSmallAux
import Certificates.Kernel.Sporadic.OddCore.ON2127

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.ONOddCore CFSG.ONSchreier CFSG.ONSchreier.Native in
open CFSG.PSL3Four.Native in
theorem certificate2127 : quotCheck (indexOf m120Enum.tabs) = true := KernelSpor.ON2127.facts2127

end Certificates
