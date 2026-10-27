module

public import Certificates.Kernel.Census.J3.Words
import all Certificates.Kernel.Census.J3.Data
import all Certificates.Kernel.Census.J3.Words
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.J3

set_option maxRecDepth 1000000

theorem kW240 : (List.range' 240 30).all wordF = true := by quickRfl
theorem kW270 : (List.range' 270 30).all wordF = true := by quickRfl

end CertificateChecks.KernelCensus.J3

end
