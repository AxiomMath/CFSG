module

public import Certificates.Kernel.ChengHeld.Pres
public import Certificates.Data.Kernel.ChengHeldCentK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelChengHeld

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.ChengHeld

@[expose] noncomputable def p256 (x y : Nat) : Nat := pcomp 256 9 (mask 9) x y

@[expose] noncomputable def xiCs (G : Nat → Nat) : List Nat :=
  [p256 (G 0) (G 0), G 1, p256 (G 0) (G 2), G 6]

@[expose] noncomputable def tPows (G : Nat → Nat) : List Nat :=
  [pidn 256 9, G 0, p256 (G 0) (G 0), p256 (p256 (G 0) (G 0)) (G 0)]

theorem x0_cent : centSqK 256 9 256 CH0.T (xiCs CH0.G) (tPows CH0.G) = true := by quickRfl

theorem x1_cent : centSqK 256 9 256 CH1.T (xiCs CH1.G) (tPows CH1.G) = true := by quickRfl

end CertificateChecks.KernelChengHeld

end
