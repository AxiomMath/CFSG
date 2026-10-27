
module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43AutCheck
import Certificates.Kernel.U43Mod.Glue3962

public section

namespace Certificates

open CertificateChecks

theorem certificate3962 : CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut.u43AutCheck () = true := KernelU43Aut3962.u43AutCheck_true

end Certificates
