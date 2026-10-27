module

public import Certificates.Kernel.ChengHeld.Sec2
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelChengHeld.S2

open CFSG.KC.ChengHeldS2

theorem k0_tw : (twK 256 m0 i0 (aR (AU0 0)) (bR m0 (zGs g0)) &&
    twK 256 m0 i0 (aR (AU0 1)) (bR m0 (zGs g0)) &&
    twK 256 m0 i0 (aR (AU0 2)) (bR m0 (zGs g0))) = true := by decide +kernel

theorem k1_tw : (twK 256 m1 i1 (aR (AU1 0)) (bR m1 (zGs g1)) &&
    twK 256 m1 i1 (aR (AU1 1)) (bR m1 (zGs g1)) &&
    twK 256 m1 i1 (aR (AU1 2)) (bR m1 (zGs g1))) = true := by decide +kernel

theorem k0_sq : sqVK 256 m0 (bR m0 (vGs m0 g0)) = true := by decide +kernel
theorem k1_sq : sqVK 256 m1 (bR m1 (vGs m1 g1)) = true := by decide +kernel

theorem k0_ea : eaCentK 256 m0 (bR m0 (vGs m0 g0)) = true := by decide +kernel
theorem k1_ea : eaCentK 256 m1 (bR m1 (vGs m1 g1)) = true := by decide +kernel

theorem k0_nc : (notCentK 256 m0 i0 (aR (AU0 0)) (bR m0 (vGs m0 g0)) &&
    notCentK 256 m0 i0 (aR (AU0 2)) (bR m0 (vGs m0 g0))) = true := by decide +kernel
theorem k1_nc : (notCentK 256 m1 i1 (aR (AU1 0)) (bR m1 (vGs m1 g1)) &&
    notCentK 256 m1 i1 (aR (AU1 2)) (bR m1 (vGs m1 g1))) = true := by decide +kernel

theorem k0_uf : unitFixK 256 (aR (AU0 2)) (bR m0 (u1Gs m0 g0)) (bR m0 (u2Gs m0 g0)) = true := by
  decide +kernel
theorem k1_uf : unitFixK 256 (aR (AU1 2)) (bR m1 (u1Gs m1 g1)) (bR m1 (u2Gs m1 g1)) = true := by
  decide +kernel

theorem k1_gr : graphK 256 m1 i1 (aR (AU1 1)) (bR m1 (vGs m1 g1)) (g1 0) = true := by
  decide +kernel

end CertificateChecks.KernelChengHeld.S2

end
