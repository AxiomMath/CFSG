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

theorem kE12 : ebF 12 = true := by quickRfl
theorem kE13 : ebF 13 = true := by quickRfl
theorem kE14 : ebF 14 = true := by quickRfl
theorem kE15 : ebF 15 = true := by quickRfl

end CertificateChecks.KernelCensus.Suz

end
