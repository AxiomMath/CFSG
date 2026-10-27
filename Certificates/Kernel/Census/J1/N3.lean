module

public import Certificates.Kernel.Census.J1.Data
import all Certificates.Kernel.Census.J1.Data
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Census.PackedF
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.J1

set_option maxRecDepth 1000000

theorem kN3 : nodeF 3 = true := by quickRfl

end CertificateChecks.KernelCensus.J1

end
