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

theorem kN32 : (List.range' 32 4).all nodeF = true := by quickRfl
theorem kN36 : (List.range' 36 4).all nodeF = true := by quickRfl
theorem kN40 : (List.range' 40 4).all nodeF = true := by quickRfl
theorem kN44 : (List.range' 44 4).all nodeF = true := by quickRfl
theorem kN48 : (List.range' 48 4).all nodeF = true := by quickRfl
theorem kN52 : (List.range' 52 4).all nodeF = true := by quickRfl
theorem kN56 : (List.range' 56 4).all nodeF = true := by quickRfl
theorem kN60 : (List.range' 60 4).all nodeF = true := by quickRfl

end CertificateChecks.KernelCensus.J3

end
