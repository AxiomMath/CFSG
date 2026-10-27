module

public import Certificates.Kernel.Census.U42.Data
import all Certificates.Kernel.Census.U42.Data
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Spor.Chain
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.U42K

open CFSG.KC.Census

set_option maxRecDepth 1000000

theorem kS : penumOK 45 6 u42SG [0, 1, 16, 3, 2, 4, 5, 6, 7] u42CS = true := by quickRfl

theorem kR : ((List.range u42CS.pts.size).all fun p =>
    prootOK 45 6 u42Nodes (pcN 45 6 u42Nodes) u42CS.pts[p]! u42Roots[p]!) = true := by quickRfl

theorem kNs : Nat.beq u42Nodes.size 199 = true := by quickRfl

theorem kSz : Nat.beq u42CS.pts.size 128 = true := by quickRfl

end CertificateChecks.KernelCensus.U42K

end
