module

public import Certificates.Kernel.Census.J3.Data
import all Certificates.Kernel.Census.J3.Data
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.PackedConjF
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.J3

set_option maxRecDepth 1000000

theorem kU0 : usF 0 = true := by quickRfl
theorem kU1 : usF 1 = true := by quickRfl
theorem kU2 : usF 2 = true := by quickRfl
theorem kU3 : usF 3 = true := by quickRfl
theorem kU4 : usF 4 = true := by quickRfl
theorem kU5 : usF 5 = true := by quickRfl
theorem kU6 : usF 6 = true := by quickRfl
theorem kU7 : usF 7 = true := by quickRfl
theorem kU8 : usF 8 = true := by quickRfl
theorem kU9 : usF 9 = true := by quickRfl
theorem kU10 : usF 10 = true := by quickRfl
theorem kU11 : usF 11 = true := by quickRfl

theorem kH0 : headF 0 = true := by quickRfl
theorem kH1 : headF 1 = true := by quickRfl
theorem kH2 : headF 2 = true := by quickRfl
theorem kH3 : headF 3 = true := by quickRfl
theorem kH4 : headF 4 = true := by quickRfl
theorem kH5 : headF 5 = true := by quickRfl
theorem kH6 : headF 6 = true := by quickRfl
theorem kH7 : headF 7 = true := by quickRfl
theorem kH8 : headF 8 = true := by quickRfl

end CertificateChecks.KernelCensus.J3

end
