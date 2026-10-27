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

theorem kN39 : (List.range' 39 13).all nodeF = true := by quickRfl
theorem kN52 : (List.range' 52 13).all nodeF = true := by quickRfl
theorem kN65 : (List.range' 65 13).all nodeF = true := by quickRfl

end CertificateChecks.KernelCensus.Co3C

end
