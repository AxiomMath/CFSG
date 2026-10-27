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

theorem kN48 : (List.range' 48 12).all nodeF = true := by quickRfl
theorem kN60 : (List.range' 60 12).all nodeF = true := by quickRfl
theorem kN72 : (List.range' 72 12).all nodeF = true := by quickRfl
theorem kN84 : (List.range' 84 12).all nodeF = true := by quickRfl
theorem kN96 : (List.range' 96 12).all nodeF = true := by quickRfl

end CertificateChecks.KernelCensus.HSC

end
