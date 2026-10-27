module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.GenD13.Data
import Certificates.Kernel.KDenseP.NortonSLP.GenD13

public section

namespace Certificates

open CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.GenD13 in
theorem certificate125541 :
    prodCheck genD13Gens genD13Steps 396 397 = true :=
  CertificateChecks.KernelKDenseP.NortonSLP.GenD13.c125541

end Certificates
