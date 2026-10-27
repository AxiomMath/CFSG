module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen13.Data
import Certificates.Kernel.KDenseP.NortonSLP.Gen13

public section

namespace Certificates

open CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.Gen13 in
theorem certificate125000 :
    prodCheck gen13Gens gen13Steps 0 76 = true :=
  CertificateChecks.KernelKDenseP.NortonSLP.Gen13.c125000

end Certificates
