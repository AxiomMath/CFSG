module

public import Certificates.Data.CFSGNative.Bridge.SurjD
import Certificates.Kernel.Co1Surj.K
public import CFSG.Assembly.LowTwoRankDefs
public import Certificates.Certificate3024Base

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic.SmallF2 CFSG.Sporadic.Bridge.SurjD.Native TauCeti in
theorem certificate8154 : co1Check () = true := KernelCo1Surj.co1Check_k

end Certificates
