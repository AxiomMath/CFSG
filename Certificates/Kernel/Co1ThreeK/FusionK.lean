module

public import Certificates.Kernel.Co1ThreeK.Fusion
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Enum CFSG.KC.Co1Cl CFSG.KS.SporSch.M24

theorem kQFus : (Nat.beq (lenLL FM.FT) 26 && allBlk 1 (fun k => fusQK 27 FM.ADT FM.TT FM.AT FM.GC
    FM.RP FM.DP k (getLL FM.FT (Nat.sub k 1))) 26) = true := by quickRfl

end CertificateChecks.KernelCo1ThreeK

end
