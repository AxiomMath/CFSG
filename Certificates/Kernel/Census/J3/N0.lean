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

theorem kN0 : (List.range' 0 4).all nodeF = true := by quickRfl
theorem kN4 : (List.range' 4 4).all nodeF = true := by quickRfl
theorem kN8 : (List.range' 8 4).all nodeF = true := by quickRfl
theorem kN12 : (List.range' 12 4).all nodeF = true := by quickRfl
theorem kN16 : (List.range' 16 4).all nodeF = true := by quickRfl
theorem kN20 : (List.range' 20 4).all nodeF = true := by quickRfl
theorem kN24 : (List.range' 24 4).all nodeF = true := by quickRfl
theorem kN28 : (List.range' 28 4).all nodeF = true := by quickRfl

end CertificateChecks.KernelCensus.J3

end
