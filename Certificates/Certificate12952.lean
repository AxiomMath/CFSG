module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin

public section

namespace CertificateChecks.Batch12952

private theorem exists_stdData_0 :
    Equiv.swap (0 : Fin 5) 1 ∈ CFSG.QuasithinUnique.A5.Delta5.Eset := by
  decide +kernel

end CertificateChecks.Batch12952

namespace Certificates

open CertificateChecks

theorem certificate12952 : Equiv.swap (0 : Fin 5) 1 ∈ CFSG.QuasithinUnique.A5.Delta5.Eset := by
  exact CertificateChecks.Batch12952.exists_stdData_0

end Certificates
