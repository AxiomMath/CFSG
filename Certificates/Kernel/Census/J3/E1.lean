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

theorem kE16 : ((j3EB.drop 16).take 2).all ebF = true := by quickRfl
theorem kE18 : ((j3EB.drop 18).take 2).all ebF = true := by quickRfl
theorem kE20 : ((j3EB.drop 20).take 2).all ebF = true := by quickRfl
theorem kE22 : ((j3EB.drop 22).take 2).all ebF = true := by quickRfl
theorem kE24 : ((j3EB.drop 24).take 2).all ebF = true := by quickRfl
theorem kE26 : ((j3EB.drop 26).take 2).all ebF = true := by quickRfl
theorem kE28 : ((j3EB.drop 28).take 2).all ebF = true := by quickRfl
theorem kE30 : ((j3EB.drop 30).take 2).all ebF = true := by quickRfl

end CertificateChecks.KernelCensus.J3

end
