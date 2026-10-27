module

public import Certificates.Kernel.Census.M2217.Data
import all Certificates.Kernel.Census.M2217.Data
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.M2217

open CFSG.KC.Census

set_option maxRecDepth 1000000

theorem kS : penumOK 24 5 m2217SG [0, 1, 2, 3, 4, 5, 8, 9] m2217CS = true := by quickRfl

theorem kR : ((List.range m2217CS.pts.size).all fun p =>
    prootOK 24 5 m2217Nodes (pcN 24 5 m2217Nodes) m2217CS.pts[p]! m2217Roots[p]!) = true := by
  quickRfl

theorem kNs : Nat.beq m2217Nodes.size 421 = true := by quickRfl

theorem kXs : Nat.beq m2217XS.size 1239 = true := by quickRfl

theorem kSz : Nat.beq m2217CS.pts.size 256 = true := by quickRfl

end CertificateChecks.KernelCensus.M2217

end
