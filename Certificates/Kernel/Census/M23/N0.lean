module

public import Certificates.Kernel.Census.M23.Data
import all Certificates.Kernel.Census.M23.Data
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Spor.Chain
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.M23K

set_option maxRecDepth 1000000

theorem kN0 : (List.range' 0 31).all nodeF = true := by quickRfl
theorem kN31 : (List.range' 31 31).all nodeF = true := by quickRfl
theorem kN62 : (List.range' 62 31).all nodeF = true := by quickRfl
theorem kN93 : (List.range' 93 31).all nodeF = true := by quickRfl

end CertificateChecks.KernelCensus.M23K

end
