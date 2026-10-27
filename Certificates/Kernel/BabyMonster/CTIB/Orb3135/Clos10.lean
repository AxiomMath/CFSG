module

public import Certificates.Kernel.BabyMonster.CTIB.Orb3135Data
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelBM.CTIB.Orb3135

open CFSG.KC.BM CFSG.KC.BM.OrbW CFSG.KD.Orb3135

theorem clos10 : ∀ t < 2016, closB act 15 1008 30240 SB EB (20160 + t) = true := by lc_cover 144

end CertificateChecks.KernelBM.CTIB.Orb3135

end
