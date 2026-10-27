module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicCertInputs
public import Certificates.Data.CFSGNative.PSL3Four.L34RLev
import Certificates.Kernel.LocalComp.L34E16F

public section

namespace Certificates

open CertificateChecks

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts in
theorem certificate33001 : l34E16Check (wordTabs wT₀) = true := KernelLC.L34E16.e16_true

end Certificates
