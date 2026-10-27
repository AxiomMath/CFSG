module

public import Certificates.Kernel.Census.J2.DataExc
import all Certificates.Kernel.Census.J2.DataExc
import all Certificates.Kernel.Census.J2.Sift
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

open CFSG.KC.Census

set_option maxRecDepth 1000000

theorem kSExc : penumOK 315 9 j2ExcSG [0, 4, 3] j2ExcCS = true := by quickRfl

theorem kRExc : ((List.range j2ExcCS.pts.size).all fun p =>
    prootOK 315 9 j2ExcNodes cNLExc j2ExcCS.pts[p]! j2ExcRoots[p]!) = true := by quickRfl

theorem kNSExc : Nat.beq j2ExcNodes.size 232 = true := by quickRfl

theorem kSzExc : Nat.beq j2ExcCS.pts.size 256 = true := by quickRfl

end CertificateChecks.KernelCensus.J2K

end
