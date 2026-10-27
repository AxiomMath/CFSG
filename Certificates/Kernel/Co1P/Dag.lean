module

public import Certificates.Kernel.Co1P.Defs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.StrLits
public import CFSG.Sporadic.Co1Patterson.GraphTreeData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KD.Co1B CFSG.KD.Co1P CFSG.KC.Co1P
  CertificateChecks.KernelCo1Cover

theorem bray_chk : dagOK [R0, R1, getL oneK IRS 23] CFSG.Sporadic.Co1Block.twoAD1 BRS59 BRIS59 = true := by
  quickRfl

theorem gdag_chk : dagOK gBaseK GWL GDS GDIS = true := by
  quickRfl

theorem gwords_text : CFSG.Sporadic.Co1Patterson.Native.gWordsText = String.ofList (wordsC GWL) := by
  str_lits CFSG.Sporadic.Co1Patterson.Native.gWordsText
  exact congrArg String.ofList (of_decide_eq_true (by quickRfl))

end CertificateChecks.KernelCo1P

end
