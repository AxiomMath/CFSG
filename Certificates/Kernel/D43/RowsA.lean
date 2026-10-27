module

public import Certificates.Data.Kernel.D43.Rows
public import Certificates.Kernel.D43.Data
import all Init.Data.Array.Basic
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.List.Basic
import all CFSG.LieType.Ree.Mirror
import all Certificates.Data.CFSGNative.Fi23.Wide

public section

namespace CertificateChecks.KernelD43

open CFSG.KC.D43 CFSG.KS.ON

theorem rows0 : rowsOK (RL.getD 0 []) 0 = true := by decide +kernel

theorem rows1 : rowsOK (RL.getD 1 []) 1 = true := by decide +kernel

theorem rows8 : rowsOK (RL.getD 8 []) 8 = true := by decide +kernel

end CertificateChecks.KernelD43

end
