module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.GenD13.Data
import Certificates.Kernel.KDenseP.NortonSLP.GenD13

public section

namespace Certificates

open CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.GenD13 in
theorem certificate125530 :
    prodCheck genD13Gens genD13Steps 0 22 = true :=
  CertificateChecks.KernelKDenseP.NortonSLP.GenD13.c125530

end Certificates
