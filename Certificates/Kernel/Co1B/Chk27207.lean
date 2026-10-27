module

public import Certificates.Kernel.Co1B.Data27207
public import Certificates.Kernel.Co1B.Dag2045
public import Certificates.Data.Kernel.Co1BSpin
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1CentData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Cent27207

open CFSG.KC.Co1BSpin CFSG.KC.Co1B CFSG.EvenSporadicStandard.Co1Cent

theorem kX : eqK K.X (mulWK (Cent2045.D2.M 19)
    (powWK (mulWK (Cent2045.D2.M 19) (Cent2045.D2.M 21)) 13)) = true := by quickRfl
theorem kY : eqK K.Y (Cent2045.D2.M 21) = true := by quickRfl
theorem kXI : Nat.beq (mulK K.X K.XI) oneK = true := by quickRfl
theorem kYI : Nat.beq (mulK K.Y K.YI) oneK = true := by quickRfl
theorem kRS : leqK K.RS (K.SW.map fun w =>
    wordK [K.X, K.Y] [K.XI, K.YI] (w.map CFSG.Sporadic.Co1Schreier.Native.decLetter)) = true := by
  quickRfl
theorem kSpin : spinK K.RS K.RIS centData.bw centData.v0 centData.sel centData.wcols.length K.AK
    K.ATK K.bK K.CP K.LP K.WC K.PP = true := by quickRfl

end CertificateChecks.KernelCo1B.Cent27207

end
