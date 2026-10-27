module

public import Certificates.Kernel.Co1B.Defs17330
public import Certificates.Kernel.Co1B.Bfs17330
public import Certificates.Kernel.Co1ThreeK.Letters
public import Certificates.Data.Kernel.SporSch.Co1Bfs
public import Certificates.Data.TabCo1ThreeB
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17330

open CFSG.KC.Co1B CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB
open CFSG.KS.SporSch.M24 (gtPinK bfsMemK)
open CFSG.KLie.CT (notB)

@[expose] noncomputable def ZM (l : Nat) : Nat := CertificateChecks.KernelCo1ThreeK.KZ.M (89 + l)

@[expose] noncomputable def wK (w : List Int) : Nat := wordK RS4 IS4 w

theorem kZT : (gtPinK ZM 2 20 ZT.N ZT.P ZT.PAR ZT.LAB ZT.W ZT.S && Nat.beq ZT.N 9) = true := by
  quickRfl

theorem kOrd : (eqK (powWK XK 3) oneK && eqK (powWK ZK 3) oneK && notB (eqK XK oneK) &&
    eqK XK (CertificateChecks.KernelCo1ThreeK.R.M 1)) = true := by quickRfl

theorem kCom : (eqK (mulWK XK AK) (mulWK AK XK) && eqK (mulWK XK BK) (mulWK BK XK) &&
    eqK (mulWK ZK AK) (mulWK AK ZK) && eqK (mulWK ZK BK) (mulWK BK ZK) &&
    eqK (mulWK XK ZK) (mulWK ZK XK) && notB (eqK (mulWK AK BK) (mulWK BK AK))) = true := by
  quickRfl

theorem kRel : relsW.all (fun w => bfsMemK ZT.P ZT.S ZT.N (wordK (RS4.take 2) (IS4.take 2) w)) =
    true := by quickRfl

theorem kInv : [wu1, wv1, wu2, wv2].all (fun w => canK (wK w) && canK (wK (invW w)) &&
    Nat.beq (mulK (wK w) (wK (invW w))) oneK) = true := by quickRfl

theorem kCm : (eqK (mulK (mulK (wK (invW wu1)) (wK (invW wv1))) (mulK (wK wu1) (wK wv1)))
      (powWK XK 2) &&
    eqK (mulK (mulK (wK (invW wu2)) (wK (invW wv2))) (mulK (wK wu2) (wK wv2))) ZK) = true := by
  quickRfl

end CertificateChecks.KernelCo1B.Bound17330

end
