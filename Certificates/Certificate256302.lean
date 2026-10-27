module

public import Certificates.Data.Inputs256cGen5
import Certificates.Kernel.Misc.Perm.HS100.G5Glue

public section

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256c

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256c in
theorem certificate256302 : hsGen5Check = true := KernelMisc.HS100.G5.hsGen5Check_true

end Certificates
