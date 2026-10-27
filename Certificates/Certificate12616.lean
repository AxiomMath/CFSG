module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.M24TcData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.M24TcData
import Certificates.Kernel.Tc.M24Facts
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M24
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M24
public meta import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.Native.FiveKit
public meta import CFSG.RankThree.Native.FiveKit
public import CFSG.Sporadic.Schreier.M24
public meta import CFSG.Sporadic.Schreier.M24
import CFSG.Certificates.Kernel.BfsPinSound

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbeddingD2.Wilson.Census219 in
theorem certificate12616 : m24TcOK () = true := KernelTc.M24.m24Tc_ok

end Certificates
