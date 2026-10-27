module

public import Certificates.Kernel.BabyMonster.CTIB.Cls3135Data
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelBM.CTIB.Cls3135

open CFSG.KC.BM CFSG.KC.BM.CosetQ CFSG.KC.BM.OrbW CFSG.KD.Cls3135

theorem cnt0 : ∀ b < 12, andB (okB chk (960 * (0 + b)) 960)
    (Nat.beq (cntB chk (960 * (0 + b)) 960) (nthN CK (0 + b))) = true := by lc_cover 1

end CertificateChecks.KernelBM.CTIB.Cls3135

end
