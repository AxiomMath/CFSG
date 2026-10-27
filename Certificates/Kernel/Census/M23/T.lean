module

public import Certificates.Kernel.Census.M23.Data
import all Certificates.Kernel.Census.M23.Data
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Spor.Chain
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.M23K

open CFSG.KC.Census

set_option maxRecDepth 1000000

theorem kS : penumOK 23 5 m23SG [0, 1, 2, 3, 4, 5, 6] m23CS = true := by quickRfl

theorem kR : ((List.range m23CS.pts.size).all fun p =>
    prootOK 23 5 m23Nodes (pcN 23 5 m23Nodes) m23CS.pts[p]! m23Roots[p]!) = true := by quickRfl

theorem kNs : Nat.beq m23Nodes.size 124 = true := by quickRfl

theorem kSz : Nat.beq m23CS.pts.size 128 = true := by quickRfl

theorem kG : ((List.range m23SG.size).all fun k =>
    canon1 23 5 m23SG[k]! && inP m23SG[k]!) = true := by quickRfl

end CertificateChecks.KernelCensus.M23K

end
