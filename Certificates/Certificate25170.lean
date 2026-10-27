module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Co1TwoBInputs
import Certificates.Kernel.Co1B.C25170

public section

namespace Certificates

open CertificateChecks

theorem certificate25170 : CFSG.EvenSporadicStandard.Solomon78.twoBCommCheck = true := KernelCo1B.Comm25170.c25170

end Certificates
