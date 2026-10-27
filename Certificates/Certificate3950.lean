module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5
import CFSG.Adapters.ProjectiveSpecialLinear

public section

open CFSG.QuasithinUnique.A5.Delta5

namespace CertificateChecks.Batch3950

open CFSG.QuasithinUnique.A5.Delta5

private theorem not_isSolvable_alt5_0 : (a0 * b0 : Equiv.Perm (Fin 5)) = b0 * a0 → False := by
  decide +kernel

end CertificateChecks.Batch3950

namespace Certificates

open CertificateChecks

open CFSG.QuasithinUnique.A5.Delta5 in
theorem certificate3950 : (a0 * b0 : Equiv.Perm (Fin 5)) = b0 * a0 → False := by
  exact CertificateChecks.Batch3950.not_isSolvable_alt5_0

end Certificates
