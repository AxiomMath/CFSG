module

public import Certificates.Kernel.Misc.Perm.J2C3A
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS155.J2E4Data
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS155.J2E4Data

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KernelC12643.X7 9 CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.x7A
#ks_perm CertificateChecks.KernelC12643.X5A 9 CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.x5aA
#ks_perm CertificateChecks.KernelC12643.X5C 9 CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.x5cA
#ks_perm CertificateChecks.KernelC12643.Y2 9 CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.y2A
#ks_perm CertificateChecks.KernelC12643.E1 9 CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.e1A
#ks_perm CertificateChecks.KernelC12643.E2 9 CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.e2A

public section

namespace CertificateChecks.KernelC12643

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155

theorem hx7 : x7A = unpack 315 9 X7 := arrBind_sound (by quickRfl)
theorem hx5a : x5aA = unpack 315 9 X5A := arrBind_sound (by quickRfl)
theorem hx5c : x5cA = unpack 315 9 X5C := arrBind_sound (by quickRfl)
theorem hy2 : y2A = unpack 315 9 Y2 := arrBind_sound (by quickRfl)
theorem he1 : e1A = unpack 315 9 E1 := arrBind_sound (by quickRfl)
theorem he2 : e2A = unpack 315 9 E2 := arrBind_sound (by quickRfl)

theorem pX7 : permB 315 9 X7 = true := by quickRfl
theorem pX5A : permB 315 9 X5A = true := by quickRfl
theorem pX5C : permB 315 9 X5C = true := by quickRfl
theorem pY2 : permB 315 9 Y2 = true := by quickRfl
theorem pE1 : permB 315 9 E1 = true := by quickRfl
theorem pE2 : permB 315 9 E2 = true := by quickRfl

end CertificateChecks.KernelC12643

end
