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

theorem kE32 : ((j3EB.drop 32).take 2).all ebF = true := by quickRfl
theorem kE34 : ((j3EB.drop 34).take 2).all ebF = true := by quickRfl
theorem kE36 : ((j3EB.drop 36).take 2).all ebF = true := by quickRfl
theorem kE38 : ((j3EB.drop 38).take 2).all ebF = true := by quickRfl
theorem kE40 : ((j3EB.drop 40).take 2).all ebF = true := by quickRfl
theorem kE42 : ((j3EB.drop 42).take 2).all ebF = true := by quickRfl
theorem kE44 : ((j3EB.drop 44).take 2).all ebF = true := by quickRfl
theorem kE46 : ((j3EB.drop 46).take 2).all ebF = true := by quickRfl

end CertificateChecks.KernelCensus.J3

end
