
module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43InvCheck
import Certificates.Kernel.U43Mod.InvGlue

public section

namespace Certificates

open CertificateChecks

theorem certificate3961 : CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv.u43InvCheck () = true := KernelU43Inv.u43InvCheck_ok

end Certificates
