module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4PrimeKernelData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4PrimeKernelData
import Certificates.Kernel.J4M2.C12603
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs
public import CFSG.Sporadic.Th.F2Spec
public meta import CFSG.Sporadic.Th.F2Spec

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier in
theorem certificate12603 : primeKerOK = true := KernelJ4PK.c12603

end Certificates
