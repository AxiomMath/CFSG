module

public import Certificates.Kernel.Co1B.In24513
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Co1TwoBInputs

public section

namespace CertificateChecks.KernelCo1B.Comm25170

open CFSG.Sporadic.Co1Schreier.Native CFSG.EvenSporadicStandard.TwoCo1.HypOne
  CFSG.EvenSporadicStandard.Solomon78 CertificateChecks.KernelCo1B.Syl2B

def dagC : List Rows × List Rows × Bool := dag (pickRows dagS sylIdxB) [twoBCommWX, twoBCommWY]

end CertificateChecks.KernelCo1B.Comm25170

end
