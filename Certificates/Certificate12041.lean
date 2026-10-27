module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CoverData
import Certificates.Kernel.OmegaEight.Mult12041

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Cover in
theorem certificate12041 : (rels.all fun r => decide (rhoWord r * rhoWord r = 1)) = true :=
  KernelO8.Mult12041.relator_sq

end Certificates
