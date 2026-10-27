
module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentRigidCheckInputs
import Certificates.Kernel.LocalComp.E3Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.SympSix.Co3Ident in
theorem certificate3096 : e3Check = true := KernelLC.Co3Id.facts3096

end Certificates
