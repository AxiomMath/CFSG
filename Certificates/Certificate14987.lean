module

public import CFSG.RankThree.PartOne.KS.Co1ScalInputs
import Certificates.Kernel.GLQ.Co1ScalFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartOne.KS.Co1Scal in
theorem certificate14987 : co1ScalCheck = true := KernelGLQ.Co1ScalK.facts14987

end Certificates
