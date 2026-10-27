module

public import Certificates.Kernel.Census.Co3C.Data
import all Certificates.Kernel.Census.Co3C.Data
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Co3C

open CFSG.KC.Census

set_option maxRecDepth 1000000

theorem kN0 : (List.range' 0 13).all nodeF = true := by quickRfl
theorem kN13 : (List.range' 13 13).all nodeF = true := by quickRfl
theorem kN26 : (List.range' 26 13).all nodeF = true := by quickRfl

end CertificateChecks.KernelCensus.Co3C

end
