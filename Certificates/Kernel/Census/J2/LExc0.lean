module

public import Certificates.Kernel.Census.J2.DataL
import all Certificates.Kernel.Census.J2.DataL
import all Certificates.Kernel.Census.J2.DataExc
import all Certificates.Kernel.Census.J2.Sift
import all Certificates.Data.Kernel.Census.PackedL
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Census.PackedExc
import all Certificates.Data.Kernel.Spor.Chain
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.J2K

set_option maxRecDepth 1000000

theorem kExcL0 : blkExcL 0 58 = true := by quickRfl
theorem kExcL58 : blkExcL 58 58 = true := by quickRfl

end CertificateChecks.KernelCensus.J2K

end
