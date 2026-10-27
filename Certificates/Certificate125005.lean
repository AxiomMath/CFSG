module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen13.Data
import Certificates.Kernel.KDenseP.NortonSLP.Gen13

public section

namespace Certificates

open CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.Gen13 in
theorem certificate125005 :
    prodCheck gen13Gens gen13Steps 278 288 = true :=
  CertificateChecks.KernelKDenseP.NortonSLP.Gen13.c125005

end Certificates
