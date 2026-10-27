module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen13.Data
import Certificates.Kernel.KDenseP.NortonSLP.Gen13

public section

namespace Certificates

open CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.Gen13 in
theorem certificate125003 :
    prodCheck gen13Gens gen13Steps 207 264 = true :=
  CertificateChecks.KernelKDenseP.NortonSLP.Gen13.c125003

end Certificates
