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

theorem kN160 : (List.range' 160 4).all nodeF = true := by quickRfl
theorem kN164 : (List.range' 164 4).all nodeF = true := by quickRfl
theorem kN168 : (List.range' 168 4).all nodeF = true := by quickRfl
theorem kN172 : (List.range' 172 4).all nodeF = true := by quickRfl
theorem kN176 : (List.range' 176 4).all nodeF = true := by quickRfl
theorem kN180 : (List.range' 180 4).all nodeF = true := by quickRfl
theorem kN184 : (List.range' 184 4).all nodeF = true := by quickRfl
theorem kN188 : (List.range' 188 4).all nodeF = true := by quickRfl

end CertificateChecks.KernelCensus.J3

end
