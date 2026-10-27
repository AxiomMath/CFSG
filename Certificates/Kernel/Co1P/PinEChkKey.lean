module

public import Certificates.Kernel.Co1P.PinEDefs
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co1Patterson.GraphTreeData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KLie.CT CFSG.Sporadic.Co1Patterson.Native

theorem recsE_pin : recsEqK recE (recsT orbEMasks) 0 = true := by quickRfl

#j4q_all CertificateChecks.KernelCo1P.KeyE CertificateChecks.KernelCo1P.keyE_chunk 197

theorem recsE_neg : notB (recsEqK (fun i => recE (i + 1)) ((recsT orbEMasks).take 64) 0) = true := by
  quickRfl

theorem hsE_neg : notB (pinAt (hsAct BK) oneK (fun i => hsE (i + 1)) recE 7) = true := by quickRfl

theorem keyE_neg : notB (keyAt 12600 64 skE (fun s => ixE (s + 1)) ptPE 3) = true := by quickRfl

theorem memE_neg : notB (memE oneK) = true := by quickRfl

theorem memE_pos : memE (ptPE 1234) = true := by quickRfl

end CertificateChecks.KernelCo1P

end
