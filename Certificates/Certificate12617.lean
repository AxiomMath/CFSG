module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.HeTcData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.HeTcData
import Certificates.Kernel.Tc.HeFacts
import Certificates.Certificate2112
import CFSG.Certificates.Kernel.SporSch.PairClTSound
import CFSG.Certificates.Kernel.SporSch.PairKSound
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeCheckBase
import CFSG.Sporadic.He
import CFSG.Sporadic.HeldB.CertPBridge
import CFSG.Sporadic.Th.F2Spec

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbeddingD2.Wilson.Census219 in
theorem certificate12617 : heTcOK () = true := KernelTc.He.heTc_ok

end Certificates
