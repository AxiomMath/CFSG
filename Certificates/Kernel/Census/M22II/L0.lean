module

public import Certificates.Kernel.Census.M22II.DataL
import all Certificates.Kernel.Census.M22II.DataL
import all Certificates.Kernel.Census.M22II.Data
import all Certificates.Data.Kernel.Census.PackedL
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.M22II

set_option maxRecDepth 1000000

theorem kL0 : blkL 0 30 = true := by quickRfl
theorem kL30 : blkL 30 30 = true := by quickRfl
theorem kL60 : blkL 60 30 = true := by quickRfl
theorem kL90 : blkL 90 30 = true := by quickRfl
theorem kL120 : blkL 120 30 = true := by quickRfl
theorem kL150 : blkL 150 30 = true := by quickRfl
theorem kL180 : blkL 180 30 = true := by quickRfl
theorem kL210 : blkL 210 30 = true := by quickRfl
theorem kL240 : blkL 240 30 = true := by quickRfl
theorem kL270 : blkL 270 30 = true := by quickRfl

end CertificateChecks.KernelCensus.M22II

end
