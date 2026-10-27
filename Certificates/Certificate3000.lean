module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaNativeData
import Certificates.Kernel.UnitarySix.Yamada

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.UnitarySix.Yamada in
theorem certificate3000 : 
      (commCheck = true)
    ∧ (transCheck = true) := KernelU6.cert3000

end Certificates
