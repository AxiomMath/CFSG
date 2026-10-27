module

public import Certificates.Kernel.Census.RuR.Data
import all Certificates.Kernel.Census.RuR.Data
import all Certificates.Data.Kernel.Census.PackedTree
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.PackedExc
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.RuR

open CFSG.KC.Census

set_option maxRecDepth 1000000

theorem kN0 : (List.range' 0 15).all nodeF = true := by quickRfl

theorem kN15 : (List.range' 15 72).all nodeF = true := by quickRfl

theorem kN87 : nodeF 87 = true := by quickRfl

theorem kN88 : (List.range' 88 46).all nodeF = true := by quickRfl

end CertificateChecks.KernelCensus.RuR

end
