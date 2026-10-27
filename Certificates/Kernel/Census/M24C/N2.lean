module

public import Certificates.Kernel.Census.M24C.Data
import all Certificates.Kernel.Census.M24C.Data
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.PackedExc
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.M24C

open CFSG.KC.Census

set_option maxRecDepth 1000000

theorem kN166 : (List.range' 166 83).all nodeF = true := by quickRfl

end CertificateChecks.KernelCensus.M24C

end
