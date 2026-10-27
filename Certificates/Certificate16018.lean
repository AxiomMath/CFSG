module

public import CFSG.Monster.AxisCount.HSIdentInputs
public import CFSG.Monster.AxisCount.CertData
public import Certificates.Certificate6007

public section

open CFSG CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.AxisCount.HS CFSG.Monster.Griess
  CFSG.Monster.B.Short

namespace CertificateChecks.Batch16018

open CFSG CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.AxisCount.HS CFSG.Monster.Griess
  CFSG.Monster.B.Short

private theorem recShards_cover_0 :
    ∀ i : Fin 12, ∀ r, r < Cert.nW i →
      ∃ s ∈ recShards, s.1 = i ∧ s.2.1 ≤ r ∧ r < s.2.2 := by
  decide +kernel

end CertificateChecks.Batch16018

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.AxisCount.HS CFSG.Monster.Griess
  CFSG.Monster.B.Short in
theorem certificate16018 : ∀ i : Fin 12, ∀ r, r < Cert.nW i →
    ∃ s ∈ recShards, s.1 = i ∧ s.2.1 ≤ r ∧ r < s.2.2 := by
  exact CertificateChecks.Batch16018.recShards_cover_0

end Certificates
