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

theorem kL300 : blkL 300 30 = true := by quickRfl
theorem kL330 : blkL 330 30 = true := by quickRfl
theorem kL360 : blkL 360 30 = true := by quickRfl
theorem kL390 : blkL 390 30 = true := by quickRfl
theorem kL420 : blkL 420 30 = true := by quickRfl
theorem kL450 : blkL 450 30 = true := by quickRfl
theorem kL480 : blkL 480 30 = true := by quickRfl
theorem kL510 : blkL 510 30 = true := by quickRfl
theorem kL540 : blkL 540 30 = true := by quickRfl
theorem kLt : blkL 570 25 = true := by quickRfl

end CertificateChecks.KernelCensus.M22II

end
