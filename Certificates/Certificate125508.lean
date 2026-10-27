module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen11.Data
import Certificates.Kernel.KDenseP.NortonSLP.Gen11

public section

namespace Certificates

open CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.Gen11 in
theorem certificate125508 :
    prodCheck gen11Gens gen11Steps 242 292 = true :=
  CertificateChecks.KernelKDenseP.NortonSLP.Gen11.c125508

end Certificates
