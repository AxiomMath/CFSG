module

public import CFSG.RankThree.PartOne.KS.HNFiveInputs
import Certificates.Kernel.GLQ.HNFiveFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartOne.KS.HNFive in
theorem certificate14985 : hnFiveCheck = true := KernelGLQ.HNFiveK.facts14985

end Certificates
