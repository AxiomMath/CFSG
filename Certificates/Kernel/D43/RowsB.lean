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

theorem rows2 : rowsOK (RL.getD 2 []) 2 = true := by decide +kernel

theorem rows3 : rowsOK (RL.getD 3 []) 3 = true := by decide +kernel

theorem rows4 : rowsOK (RL.getD 4 []) 4 = true := by decide +kernel

end CertificateChecks.KernelD43

end
