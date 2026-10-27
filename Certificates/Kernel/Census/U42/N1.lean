module

public import Certificates.Kernel.Census.U42.Data
import all Certificates.Kernel.Census.U42.Data
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Spor.Chain
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.U42K

set_option maxRecDepth 1000000

theorem kN100 : (List.range' 100 20).all nodeF = true := by quickRfl
theorem kN120 : (List.range' 120 20).all nodeF = true := by quickRfl
theorem kN140 : (List.range' 140 20).all nodeF = true := by quickRfl
theorem kN160 : (List.range' 160 20).all nodeF = true := by quickRfl
theorem kNt : (List.range' 180 19).all nodeF = true := by quickRfl

end CertificateChecks.KernelCensus.U42K

end
