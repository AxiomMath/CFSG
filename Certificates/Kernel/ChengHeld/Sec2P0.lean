module

public import Certificates.Kernel.ChengHeld.Sec2
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.ChengHeld.Sec2PB
import Certificates.Kernel.SporSch.Ru.RowsGen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelChengHeld.S2

open CFSG.KC.ChengHeldS2

@[expose] noncomputable def pf0 (j : ℕ) : Bool :=
  pfBlkC 256 m0 i0 (aR (AU0 0)) (aR (AU0 1)) (j * 32) 32

end CertificateChecks.KernelChengHeld.S2

#kss_each CertificateChecks.KernelChengHeld.S2.PF0 CertificateChecks.KernelChengHeld.S2.pf0 8

namespace CertificateChecks.KernelChengHeld.S2

open CFSG.KC.ChengHeldS2

theorem k0_pf : pairFixK 256 m0 i0 (aR (AU0 0)) (aR (AU0 1)) = true :=
  pairFixK_of_blocks 256 m0 i0 32 8 rfl fun j hj => PF0.all j hj

end CertificateChecks.KernelChengHeld.S2

end
