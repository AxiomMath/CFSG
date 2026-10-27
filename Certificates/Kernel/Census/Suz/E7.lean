module

public import Certificates.Kernel.Census.Suz.Data
import all Certificates.Kernel.Census.Suz.Data
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Census.PackedConj
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Suz

set_option maxRecDepth 1000000

theorem kE28 : ebF 28 = true := by quickRfl
theorem kE29 : ebF 29 = true := by quickRfl
theorem kE30 : ebF 30 = true := by quickRfl
theorem kE31 : ebF 31 = true := by quickRfl

end CertificateChecks.KernelCensus.Suz

end
