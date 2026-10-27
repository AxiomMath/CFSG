module

public import Certificates.Data.GH74IvkL34
public meta import Certificates.Data.GH74IvkL34
import Certificates.Kernel.LocalComp.L34RC.Glue
import CFSG.Certificates.Kernel.Spor.BfsReplay

namespace CertificateChecks.Batch5158

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelLC.L34X
  CertificateChecks.KernelLC.L34Cert CertificateChecks.KernelLC.L34RC
open CertificateChecks.KernelLC.L34Scan (canonC)
open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts

theorem all_eq (T : Array Tab) (p : Tab → Bool) : T.all p = allBelow T.size fun k => p T[k]! := by
  rw [Bool.eq_iff_iff, Array.all_eq_true, CFSG.KS.BfsReplay.allBelow_iff]
  refine forall_congr' fun k => ⟨fun h hk => ?_, fun h hk => ?_⟩
  · rw [getElem!_pos T k hk]
    exact h hk
  · have h' := h hk
    rw [getElem!_pos T k hk] at h'
    exact h'

theorem centCheck_eq (r : Tab) (C T : Array Tab) :
    Certificates.IvkL34.centCheck r C T = centOK T r C := by
  unfold Certificates.IvkL34.centCheck centOK
  rw [all_eq]
  refine congrArg (allBelow T.size) (funext fun k => ?_)
  rw [all_eq C]
  simp only [Certificates.IvkL34.commB, commT, Bool.not_and, Bool.or_assoc]

end CertificateChecks.Batch5158

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelLC.L34Cert CertificateChecks.KernelLC.L34RC
open CertificateChecks.KernelLC.L34Scan (canonC)

theorem certificate5158 : IvkL34.l34CentOK = true := by
  unfold Certificates.IvkL34.l34CentOK
  rw [CertificateChecks.Batch5158.centCheck_eq, CertificateChecks.Batch5158.centCheck_eq, hR.1, hS.1, cent2, cent3, r2_eq, r3_eq,
    cen_sound pinR.canon canonC.2.1 (cnRP (by decide)) fun i hi => (parts hi).2.1,
    cen_sound pinR.canon canonC.2.2 (cnRP (by decide)) fun i hi => (parts hi).2.2.1]
  rfl

end Certificates
