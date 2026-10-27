module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.Gen7.Data
import Certificates.Kernel.KDenseP.NortonSLP.Gen7

public section

namespace Certificates

open CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.MON5_7.Gen7 in
theorem certificate125351 :
    prodTargetsCheck gen7Gens gen7Steps 349 gen7Targets = true :=
  CertificateChecks.KernelKDenseP.NortonSLP.Gen7.c125351

end Certificates
