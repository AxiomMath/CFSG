module

public import Certificates.Kernel.Census.M2217.DataL
import all Certificates.Kernel.Census.M2217.DataL
import all Certificates.Kernel.Census.M2217.Data
import all Certificates.Data.Kernel.Census.PackedL
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.M2217

set_option maxRecDepth 1000000

theorem kL210 : blkL 210 30 = true := by quickRfl
theorem kL240 : blkL 240 30 = true := by quickRfl
theorem kL270 : blkL 270 30 = true := by quickRfl
theorem kL300 : blkL 300 30 = true := by quickRfl
theorem kL330 : blkL 330 30 = true := by quickRfl
theorem kL360 : blkL 360 30 = true := by quickRfl
theorem kL390 : blkL 390 30 = true := by quickRfl
theorem kLt : blkL 420 1 = true := by quickRfl

end CertificateChecks.KernelCensus.M2217

end
