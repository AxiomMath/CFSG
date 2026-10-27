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

set_option maxRecDepth 1000000

theorem kN0 : (List.range' 0 61).all nodeF = true := by quickRfl
theorem kN61 : (List.range' 61 61).all nodeF = true := by quickRfl

end CertificateChecks.KernelCensus.M12K

end
