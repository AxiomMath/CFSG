module

public import Certificates.Kernel.Census.HSC.Data
import all Certificates.Kernel.Census.HSC.Data
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.HSC

open CFSG.KC.Census

set_option maxRecDepth 1000000

theorem kN0 : (List.range' 0 12).all nodeF = true := by quickRfl
theorem kN12 : (List.range' 12 12).all nodeF = true := by quickRfl
theorem kN24 : (List.range' 24 12).all nodeF = true := by quickRfl
theorem kN36 : (List.range' 36 12).all nodeF = true := by quickRfl

end CertificateChecks.KernelCensus.HSC

end
