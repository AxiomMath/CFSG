module

public import Certificates.Data.Kernel.Co1PumpFus
public import Certificates.Kernel.Co1Pump.Data
public import Certificates.Kernel.Co1ThreeK.Letters
public import Certificates.Kernel.SporSch.Co1.ElemDag
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Pump

open CFSG.KC.Co1Pairs CFSG.KD.Co1Pump CertificateChecks.KernelCo1ThreeK
open CertificateChecks.KernelSporSch.Co1Elem (AF)

@[expose] noncomputable def ch36909G (i : Nat) : Nat := L.M (Nat.add 6 i)

theorem ch36909f : fusOK [AF 0, AF 1, AF 2, AF 3, AF 4, AF 5] ch36909G D recs 1 = true := by
  quickRfl

end CertificateChecks.KernelCo1Pump

end
