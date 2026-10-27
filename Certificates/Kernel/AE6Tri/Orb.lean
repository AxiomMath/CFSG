module

public import Certificates.Data.Kernel.AE6Tri.Defs
public import Certificates.Kernel.AE6Tri.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
namespace CertificateChecks.KernelAE6Tri

open CFSG.KC.AE6Tri CFSG.KD.AE6Tri

theorem kOrbV0 : bAnd(rowsOK RG orbV0 253 0 true, Nat.beq (chainCnt orbV0) 1290240) = true := by
  quickRfl

theorem kOrbE0 : bAnd(rowsOK RG orbE0 125 0 true, Nat.beq (chainCnt orbE0) 86016) = true := by
  quickRfl

theorem kInv : allIx vl (fun l L => invB RG L (triB.getD l [])) 0 = true := by quickRfl

theorem kDistV : bAnd(distB RG (distV.getD 0 []) (triB.getD 1 []),
    bAnd(distB RG (distV.getD 1 []) (triB.getD 2 []), distB RG (distV.getD 2 []) (triB.getD 2 []))) =
    true := by quickRfl

theorem kDistE : bAnd(distB RG (distE.getD 0 []) (triB.getD 2 []),
    bAnd(distB RG (distE.getD 1 []) (triB.getD 1 []), distB RG (distE.getD 2 []) (triB.getD 0 []))) =
    true := by quickRfl

end CertificateChecks.KernelAE6Tri

end
