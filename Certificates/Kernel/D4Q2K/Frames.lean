module

public import Certificates.Data.Kernel.D4Q2K.Defs
public import Certificates.Kernel.D4Q2K.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4Q2K

open CFSG.KC.D4Q2K

theorem ch709441fr : frameK D.pts D.frames.toList = true := by
  quickRfl

theorem ch709441len : bAnd(Nat.beq (lenL D.pts) 2240, Nat.beq D.frames.toList.length 4480) = true := by
  quickRfl

theorem ch709441fr_negRep : (!frameK D.pts (#[0, 0, 1, 2] :: D.frames.toList)) = true := by
  quickRfl

theorem ch709441fr_negIdx : (!frameK D.pts (#[2240, 0, 1, 2] :: D.frames.toList)) = true := by
  quickRfl

end CertificateChecks.KernelD4Q2K

end
