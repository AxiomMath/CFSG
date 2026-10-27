
module

public import Certificates.Certificate3054Base


public section

open CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Co2 CFSG.KC.SortTree CFSG.KLie.CT CFSG.KC.Bfs
  CFSG.KC.MatConj CFSG.Monster.B.TwoA.Census

namespace CertificateChecks.Batch3054

open CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Co2 CFSG.KC.SortTree CFSG.KLie.CT CFSG.KC.Bfs
  CFSG.KC.MatConj CFSG.Monster.B.TwoA.Census

set_option maxRecDepth 100000

end CertificateChecks.Batch3054

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Co2Inv in
theorem certificate3054 : conjCheck = true := by
  rw [conjCheck]
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨CertificateChecks.Batch3054.facts.1, CertificateChecks.Batch3054.facts.2⟩, CertificateChecks.Batch3054.kInvOK⟩, CertificateChecks.Batch3054.kRootRows⟩

end Certificates
