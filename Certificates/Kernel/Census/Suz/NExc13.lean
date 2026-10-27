module

public import Certificates.Kernel.Census.Suz.DataExc
public import Certificates.Kernel.Census.Suz.Sift
import all Certificates.Kernel.Census.Suz.Data
import all Certificates.Kernel.Census.Suz.DataExc
import all Certificates.Kernel.Census.Suz.Sift
import all Certificates.Kernel.Sporadic.Suz.Chain2306
import all Certificates.Kernel.Sporadic.Suz.Text2306
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Census.PackedExc
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Spor.Chain
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Suz

set_option maxRecDepth 1000000

theorem kNExc161 : (List.range' 161 6).all (nodeQ false conjExc suzE0P) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Suz

end
