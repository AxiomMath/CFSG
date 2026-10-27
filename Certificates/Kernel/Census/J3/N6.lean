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

theorem kN192 : (List.range' 192 4).all nodeF = true := by quickRfl
theorem kN196 : (List.range' 196 4).all nodeF = true := by quickRfl
theorem kN200 : (List.range' 200 4).all nodeF = true := by quickRfl
theorem kN204 : (List.range' 204 4).all nodeF = true := by quickRfl

end CertificateChecks.KernelCensus.J3

end
