module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ElevenRotCheckDefs
import Certificates.Kernel.KDenseP.Norton41508

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure in
theorem certificate41508 : elevenRotCheck () = true := KernelKDenseP.Norton41508.c41508

end Certificates
