module

public import Certificates.Kernel.Census.M12.Data
import all Certificates.Kernel.Census.M12.Data
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Census.PackedExc
import all Certificates.Data.Kernel.Spor.Chain
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.M12K

open CFSG.KC.Census

set_option maxRecDepth 1000000

theorem kS : penumOK 24 5 m12SG [0, 1, 2, 3, 4, 12, 13, 14, 15, 16] m12CS = true := by quickRfl

theorem kR : ((List.range m12CS.pts.size).all fun p =>
    prootOK 24 5 m12Nodes (pcN 24 5 m12Nodes) m12CS.pts[p]! m12Roots[p]!) = true := by quickRfl

theorem kNs : Nat.beq m12Nodes.size 122 = true := by quickRfl

theorem kSz : Nat.beq m12CS.pts.size 128 = true := by quickRfl

theorem kG : ((List.range m12SG.size).all fun k => canon1 24 5 m12SG[k]! && inRP m12SG[k]!) =
    true := by quickRfl

end CertificateChecks.KernelCensus.M12K

end
