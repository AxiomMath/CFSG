module

public import Certificates.Data.Kernel.SporSch.Co1MatW
public import Certificates.Data.CFSGNative.Timmesfeld.Co1Seven
public import Certificates.Kernel.SporSch.Co1.Packed
public meta import Certificates.Kernel.SporSch.Co1.GenDag
public meta import Certificates.Data.CFSGNative.Timmesfeld.Co1Seven
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocalInputs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Co1.GenDag

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1SevenK

open CFSG.Sporadic.Co1Schreier.Native

meta def dagD : List Rows × List Rows × Bool := Timmesfeld.Co1Seven.gDag aR bR

end CertificateChecks.KernelCo1SevenK

#kss_co1dag CertificateChecks.KernelCo1SevenK.D CertificateChecks.KernelCo1SevenK.dagD

namespace CertificateChecks.KernelCo1SevenK

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CertificateChecks.KernelSporSch.Co1Packed

theorem kBase : (Nat.beq (D.M 0) PA && Nat.beq (D.M 1) PB) = true := by quickRfl

theorem kDag : dagWK D.M D.MI 2 D.N Timmesfeld.Co1Seven.dagWords = true := by quickRfl

end CertificateChecks.KernelCo1SevenK

end
