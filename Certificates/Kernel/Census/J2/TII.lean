module

public import Certificates.Kernel.Census.J2.DataII
import all Certificates.Kernel.Census.J2.DataII
import all Certificates.Kernel.Census.J2.Sift
import all Certificates.Data.Kernel.Census.Packed
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

theorem kSII : penumOK 315 9 j2IISG [0, 4, 3] j2IICS = true := by quickRfl

theorem kRII : ((List.range j2IICS.pts.size).all fun p =>
    prootOK 315 9 j2IINodes cNLII j2IICS.pts[p]! j2IIRoots[p]!) = true := by quickRfl

theorem kNSII : Nat.beq j2IINodes.size 232 = true := by quickRfl

theorem kSzII : Nat.beq j2IICS.pts.size 256 = true := by quickRfl

end CertificateChecks.KernelCensus.J2K

end
