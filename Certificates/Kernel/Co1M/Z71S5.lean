module

public import Certificates.Data.Kernel.Co1Odd71
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1Odd

theorem z71_pts5 : ptsOK71 Z1G Z1P Z1Par Z1Lab 1232 112 = true := by quickRfl

theorem z71_nc5 : ncsOK71 Z1P Z1W 1232 112 = true := by quickRfl

theorem z71_can5 : canonsL Z1P 1232 112 = true := by quickRfl

end CertificateChecks.KernelCo1M

end
