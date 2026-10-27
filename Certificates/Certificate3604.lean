module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3EData
import Certificates.Kernel.UnitarySix.Sec3.Sound.Elt3604

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelU6.Sec3

open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native in
theorem certificate3604 : (eNativeCheck = true)
    ∧ (eTransCheck = true) := ⟨eNative_k', eTrans_k'⟩

end Certificates
