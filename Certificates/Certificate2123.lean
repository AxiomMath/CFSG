module

public import CFSG.Sporadic.ONOddCore.LocalAutDataCheckInputs
import Certificates.Kernel.Sporadic.OddCore.ON2123T

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.ONOddCore CFSG.ONSchreier.Native in
theorem certificate2123 : localFormOK localCert = true := KernelSpor.ON2123.facts2123_proved

end Certificates
