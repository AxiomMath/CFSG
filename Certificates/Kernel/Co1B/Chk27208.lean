module

public import Certificates.Kernel.Co1B.Data27207
public import Certificates.Data.Kernel.Co1BSpin
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1CentData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Cent27207

open CFSG.KC.Co1BSpin CFSG.EvenSporadicStandard.Co1Cent CFSG.Sporadic.Co1Block

theorem kClass : classK K.ATK K.CX K.CP K.WC K.X K.A1 twoBTris gdX singRecs exclRecs = true := by
  quickRfl

end CertificateChecks.KernelCo1B.Cent27207

end
