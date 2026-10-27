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

theorem kN64 : (List.range' 64 4).all nodeF = true := by quickRfl
theorem kN68 : (List.range' 68 4).all nodeF = true := by quickRfl
theorem kN72 : (List.range' 72 4).all nodeF = true := by quickRfl
theorem kN76 : (List.range' 76 4).all nodeF = true := by quickRfl
theorem kN80 : (List.range' 80 4).all nodeF = true := by quickRfl
theorem kN84 : (List.range' 84 4).all nodeF = true := by quickRfl
theorem kN88 : (List.range' 88 4).all nodeF = true := by quickRfl
theorem kN92 : (List.range' 92 4).all nodeF = true := by quickRfl

end CertificateChecks.KernelCensus.J3

end
