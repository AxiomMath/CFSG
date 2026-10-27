
module

public import Certificates.Certificate3055Base

public import CFSG.Monster.B.TwoA.Co2Inv.FrameCertInputs
public import CFSG.Certificates.Kernel.SortTreeMul
public import CFSG.Certificates.Kernel.MonsterB.U6OrbSound
public import Certificates.Kernel.MonsterB.Frame3055K
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.TwoA.Census CFSG.KC.SortTree CFSG.KLie.CT
  CFSG.KC.U6Orb CFSG.KC.Bfs

namespace CertificateChecks.Batch3055

open CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.TwoA.Census CFSG.KC.SortTree CFSG.KLie.CT
  CFSG.KC.U6Orb CFSG.KC.Bfs

set_option maxRecDepth 100000

open Frame3055 (actM recF edgeF)

end CertificateChecks.Batch3055

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Co2Inv in
theorem certificate3055 : (frameCheck = true)
    ∧ (fCheck = true) := by
  refine ⟨?_, CertificateChecks.Batch3055.group⟩
  simp only [CFSG.Monster.B.TwoA.Co2Inv.frameCheck, Bool.and_eq_true, beq_iff_eq]
  exact CertificateChecks.Batch3055.frame

end Certificates
