module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Y14Data
import Certificates.Kernel.UnitarySix.Sec3.K3605

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelU6.Sec3

open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native in
theorem certificate3605 : (y14Check = true) := y14_k

end Certificates
