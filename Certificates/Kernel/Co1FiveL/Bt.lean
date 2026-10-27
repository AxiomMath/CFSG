module

public import Certificates.Kernel.Co1FiveL.Data
public import Certificates.Kernel.Co1FiveK.Data
public import Certificates.Data.Kernel.Co1FiveL
public import Certificates.Data.CFSGNative.Timmesfeld.Co1Five
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1FiveL

open CFSG.KC.Co1FiveL CFSG.KD.Co1FiveL Timmesfeld.Co1Five

@[expose] noncomputable def ATL : List Nat := CertificateChecks.KernelCo1FiveK.FW.AT

theorem kBT0 : btK ATL (repA.getD 0 0) (repB.getD 0 0) BT0 = true := by quickRfl

theorem kBT1 : btK ATL (repA.getD 1 0) (repB.getD 1 0) BT1 = true := by quickRfl

theorem kBT2 : btK ATL (repA.getD 2 0) (repB.getD 2 0) BT2 = true := by quickRfl

end CertificateChecks.KernelCo1FiveL

end
