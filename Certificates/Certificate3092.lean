module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentBridgeInputs
import Certificates.Kernel.LocalComp.Co3SurjK
import Certificates.Kernel.LocalComp.Co3SurjChecks
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Bridge.SurjD.Native CFSG.EvenSmallLie.SympSix.Co3Ident in
theorem certificate3092 : seedLetterChecks CFSG.Sporadic.Co3.Native.co3Data vSpec = true := KernelLC.Co3Surj.facts3092

end Certificates
