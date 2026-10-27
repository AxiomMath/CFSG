module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4FixedData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4FixedData
import Certificates.Kernel.SporSch.J4S.Fix3
public meta import CFSG.Sporadic.Schreier.J4SThreeDataBase
public import CFSG.Sporadic.Schreier.J4SThreeDataBase

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier in
theorem certificate12601 : q3FixOK Q3GenPairs = true := KernelSporSch.J4Fix3.q3FixOK_true

end Certificates
