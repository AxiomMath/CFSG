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

theorem kE48 : ((j3EB.drop 48).take 2).all ebF = true := by quickRfl
theorem kE50 : ((j3EB.drop 50).take 2).all ebF = true := by quickRfl
theorem kE52 : ((j3EB.drop 52).take 2).all ebF = true := by quickRfl
theorem kE54 : ((j3EB.drop 54).take 2).all ebF = true := by quickRfl
theorem kE56 : ((j3EB.drop 56).take 2).all ebF = true := by quickRfl
theorem kE58 : ((j3EB.drop 58).take 2).all ebF = true := by quickRfl
theorem kE60 : ((j3EB.drop 60).take 2).all ebF = true := by quickRfl

end CertificateChecks.KernelCensus.J3

end
