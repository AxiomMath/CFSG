
module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43OutCheck
import Certificates.Kernel.U43Mod.OutGlue

public section

namespace Certificates

open CertificateChecks

theorem certificate13005 : CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Out.u43OutCheck () = true := KernelU43Out.u43OutCheck_ok

end Certificates
