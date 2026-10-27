module

public import CFSG.Monster.B.Classical.E6AdjointTable

public section

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Classical CFSG.Monster.B.Classical.E6Adjoint

namespace CertificateChecks.Batch1953

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Classical CFSG.Monster.B.Classical.E6Adjoint

private theorem jacRows_0_0 : jacRows 0 13 = true := by
  decide +kernel

private theorem jacRows_13_1 : jacRows 13 13 = true := by
  decide +kernel

private theorem jacRows_26_2 : jacRows 26 13 = true := by
  decide +kernel

private theorem jacRows_39_3 : jacRows 39 13 = true := by
  decide +kernel

private theorem jacRows_52_4 : jacRows 52 13 = true := by
  decide +kernel

private theorem jacRows_65_5 : jacRows 65 13 = true := by
  decide +kernel

end CertificateChecks.Batch1953

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Classical CFSG.Monster.B.Classical.E6Adjoint in
theorem certificate1953 : (jacRows 0 13 = true)
    ∧ (jacRows 13 13 = true)
    ∧ (jacRows 26 13 = true)
    ∧ (jacRows 39 13 = true)
    ∧ (jacRows 52 13 = true)
    ∧ (jacRows 65 13 = true) := by
  exact ⟨CertificateChecks.Batch1953.jacRows_0_0, CertificateChecks.Batch1953.jacRows_13_1, CertificateChecks.Batch1953.jacRows_26_2, CertificateChecks.Batch1953.jacRows_39_3, CertificateChecks.Batch1953.jacRows_52_4, CertificateChecks.Batch1953.jacRows_65_5⟩

end Certificates
