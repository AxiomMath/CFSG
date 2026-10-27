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

theorem kN96 : (List.range' 96 4).all nodeF = true := by quickRfl
theorem kN100 : (List.range' 100 4).all nodeF = true := by quickRfl
theorem kN104 : (List.range' 104 4).all nodeF = true := by quickRfl
theorem kN108 : (List.range' 108 4).all nodeF = true := by quickRfl
theorem kN112 : (List.range' 112 4).all nodeF = true := by quickRfl
theorem kN116 : (List.range' 116 4).all nodeF = true := by quickRfl
theorem kN120 : (List.range' 120 4).all nodeF = true := by quickRfl
theorem kN124 : (List.range' 124 4).all nodeF = true := by quickRfl

end CertificateChecks.KernelCensus.J3

end
