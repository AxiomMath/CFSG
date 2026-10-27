module

public import CFSG.RankThree.PartOne.KS.LyScalInputs
import Certificates.Kernel.GLQ.LyScalFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartOne.KS.LyScal in
theorem certificate14986 : lyScalCheck = true := KernelGLQ.LyScalK.facts14986

end Certificates
