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

theorem kN128 : (List.range' 128 4).all nodeF = true := by quickRfl
theorem kN132 : (List.range' 132 4).all nodeF = true := by quickRfl
theorem kN136 : (List.range' 136 4).all nodeF = true := by quickRfl
theorem kN140 : (List.range' 140 4).all nodeF = true := by quickRfl
theorem kN144 : (List.range' 144 4).all nodeF = true := by quickRfl
theorem kN148 : (List.range' 148 4).all nodeF = true := by quickRfl
theorem kN152 : (List.range' 152 4).all nodeF = true := by quickRfl
theorem kN156 : (List.range' 156 4).all nodeF = true := by quickRfl

end CertificateChecks.KernelCensus.J3

end
