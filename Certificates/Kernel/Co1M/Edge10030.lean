module

public import Certificates.Kernel.Co1M.Orb98280
public import Certificates.Kernel.Co1M.Data10030
public import Certificates.Data.Kernel.GmsEdgeK
import Certificates.Kernel.LocalComp.BlockTac

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.GmsPath CFSG.KD.Co1M

@[expose] noncomputable def edge30 (j : Nat) : Bool :=
  CFSG.KC.M1F2.strictB (CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.Pt 32 j) fun v =>
    CFSG.KLie.CT.andB (edgeV ETA EDA EF0 EMA EYA EBA EPA v) (edgeV ETC EDC EF0 EMC EYC EBC EPC v)

theorem edge30All : ∀ j < 98280, edge30 j = true := by lc_cover 256

end CertificateChecks.KernelCo1M

end
