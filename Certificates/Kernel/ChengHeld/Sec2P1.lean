module

public import Certificates.Kernel.ChengHeld.Sec2
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.ChengHeld.Sec2PB
import Certificates.Kernel.SporSch.Ru.RowsGen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelChengHeld.S2

open CFSG.KC.ChengHeldS2

@[expose] noncomputable def pf1 (j : ℕ) : Bool :=
  pfBlkC 256 m1 i1 (aR (AU1 0)) (aR (AU1 1)) (j * 32) 32

end CertificateChecks.KernelChengHeld.S2

#kss_each CertificateChecks.KernelChengHeld.S2.PF1 CertificateChecks.KernelChengHeld.S2.pf1 8

namespace CertificateChecks.KernelChengHeld.S2

open CFSG.KC.ChengHeldS2

theorem k1_pf : pairFixK 256 m1 i1 (aR (AU1 0)) (aR (AU1 1)) = true :=
  pairFixK_of_blocks 256 m1 i1 32 8 rfl fun j hj => PF1.all j hj

end CertificateChecks.KernelChengHeld.S2

end
