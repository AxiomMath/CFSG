module

public import CFSG.Monster.B.GSide.HInnerFusionI3CertInputs
import Certificates.Kernel.BabyMonster.CTIB.Frame3135A
import Certificates.Kernel.BabyMonster.CTIB.Frame3135B

public section

open CFSG.Monster.B.GSide CFSG.Monster.B.CTIB CFSG.Monster.B.CTIB.Native
  CertificateChecks.KernelBM.CTIB.Frame3135

namespace CertificateChecks.Batch3135

open CFSG.Monster.B.GSide CFSG.Monster.B.CTIB CFSG.Monster.B.CTIB.Native
  CertificateChecks.KernelBM.CTIB.Frame3135

private theorem i3CertOK_eq_true : i3CertOK innerTab = true := by
  have hC := KernelBM.census_orbitLists
  have e1 : (34560 + 1 : ℕ) = 34561 := rfl
  have e2 : (64 + 1 : ℕ) = 65 := rfl
  unfold i3CertOK frameBOK fusePts6
  rw [e1, e2]
  simp only [KernelBM.CTIB.Hist.frameA_count hC, filt hC, all8 hC, comm854 hC, mem43, fix_all,
    bfs854.1, bfs854.2, beq_self_eq_true, Bool.and_self]

end CertificateChecks.Batch3135

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.GSide CFSG.Monster.B.CTIB in
theorem certificate3135 : i3CertOK innerTab = true := CertificateChecks.Batch3135.i3CertOK_eq_true

end Certificates
