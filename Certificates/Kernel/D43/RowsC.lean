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

open CFSG.KC.D43

theorem rows5 : rowsOK (RL.getD 5 []) 5 = true := by decide +kernel

theorem rows6 : rowsOK (RL.getD 6 []) 6 = true := by decide +kernel

theorem rows7 : rowsOK (RL.getD 7 []) 7 = true := by decide +kernel

end CertificateChecks.KernelD43

end
