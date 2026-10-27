module

public import Certificates.Data.B3Spor3.HeWords
public meta import Certificates.Data.B3Spor3.HeWords
import Certificates.Certificate2112
import Certificates.Kernel.SporSch.HeThree.C0WordsFacts
import CFSG.Certificates.Kernel.Misc.ArrBind

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem certificate36901 : heC0WordsCheck = true := KernelSporSch.HeThree.c0Words

end Certificates
