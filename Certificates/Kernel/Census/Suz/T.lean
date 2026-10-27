module

public import Certificates.Kernel.Census.Suz.Sift
import all Certificates.Kernel.Census.Suz.Data
import all Certificates.Kernel.Census.Suz.Sift
import all Certificates.Kernel.Sporadic.Suz.Chain2306
import all Certificates.Kernel.Sporadic.Suz.Text2306
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Spor.Chain
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
import all CFSG.Certificates.Kernel.Enum.Defs
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Suz

open CFSG.KC.Census CertificateChecks.KernelSpor

set_option maxRecDepth 1000000

theorem kG : suzXs.all (fun x => inMP x || inMP (pc 1782 11 Suz2306.V x)) = true := by quickRfl

theorem kVV : pvalid 1782 11 Suz2306.V = true := by quickRfl

theorem kXV : suzXs.all (pvalid 1782 11) = true := by quickRfl

end CertificateChecks.KernelCensus.Suz

end
