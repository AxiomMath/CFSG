module

public import Certificates.Kernel.Census.Suz.Data
import all Certificates.Kernel.Census.Suz.Data
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Census.PackedConj
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Suz

open CFSG.KC.Census

set_option maxRecDepth 1000000

theorem kC0 : csF 0 = true := by quickRfl
theorem kC1 : csF 1 = true := by quickRfl
theorem kC2 : csF 2 = true := by quickRfl
theorem kC3 : csF 3 = true := by quickRfl

theorem kCI : (suzCi.toList.zip suzCs.toList).all
    (fun p => Nat.beq (pc 1782 11 p.1 p.2) (pid 1782 11)) = true := by
  quickRfl

theorem kR0 : rootsF 0 = true := by quickRfl
theorem kR1 : rootsF 1 = true := by quickRfl
theorem kR2 : rootsF 2 = true := by quickRfl
theorem kR3 : rootsF 3 = true := by quickRfl

end CertificateChecks.KernelCensus.Suz

end
