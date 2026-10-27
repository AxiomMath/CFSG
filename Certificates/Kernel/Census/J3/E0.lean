module

public import Certificates.Kernel.Census.J3.Data
import all Certificates.Kernel.Census.J3.Data
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Census.PackedConj
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.J3

set_option maxRecDepth 1000000

theorem kE0 : ((j3EB.drop 0).take 2).all ebF = true := by quickRfl
theorem kE2 : ((j3EB.drop 2).take 2).all ebF = true := by quickRfl
theorem kE4 : ((j3EB.drop 4).take 2).all ebF = true := by quickRfl
theorem kE6 : ((j3EB.drop 6).take 2).all ebF = true := by quickRfl
theorem kE8 : ((j3EB.drop 8).take 2).all ebF = true := by quickRfl
theorem kE10 : ((j3EB.drop 10).take 2).all ebF = true := by quickRfl
theorem kE12 : ((j3EB.drop 12).take 2).all ebF = true := by quickRfl
theorem kE14 : ((j3EB.drop 14).take 2).all ebF = true := by quickRfl

end CertificateChecks.KernelCensus.J3

end
