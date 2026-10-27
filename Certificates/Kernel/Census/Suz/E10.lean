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

theorem kE40 : ebF 40 = true := by quickRfl
theorem kE41 : ebF 41 = true := by quickRfl
theorem kE42 : ebF 42 = true := by quickRfl
theorem kE43 : ebF 43 = true := by quickRfl

end CertificateChecks.KernelCensus.Suz

end
