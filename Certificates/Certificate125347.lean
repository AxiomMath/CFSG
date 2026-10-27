module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.Gen7.Data
import Certificates.Kernel.KDenseP.NortonSLP.Gen7

public section

namespace Certificates

open CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.MON5_7.Gen7 in
theorem certificate125347 :
    prodCheck gen7Gens gen7Steps 286 302 = true :=
  CertificateChecks.KernelKDenseP.NortonSLP.Gen7.c125347

end Certificates
