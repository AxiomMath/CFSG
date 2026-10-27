module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.Gen7.Data
import Certificates.Kernel.KDenseP.NortonSLP.Gen7

public section

namespace Certificates

open CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.MON5_7.Gen7 in
theorem certificate125341 :
    prodCheck gen7Gens gen7Steps 21 31 = true :=
  CertificateChecks.KernelKDenseP.NortonSLP.Gen7.c125341

end Certificates
