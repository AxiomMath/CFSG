module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2D1Check
import Certificates.Kernel.SchreierFam.C129080K

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2 CFSG.KS.MatRep
  CertificateChecks.KernelSporSch.Co2M CertificateChecks.KernelSchreierFam.Co2Slp CFSG.KS.Co2M

namespace CertificateChecks.Batch129080

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2 CFSG.KS.MatRep
  CertificateChecks.KernelSporSch.Co2M CertificateChecks.KernelSchreierFam.Co2Slp CFSG.KS.Co2M

theorem repB : RepT 22 CFSG.Sporadic.Co2Cert.co2PackedVecs (d1Base ()) d1T := by
  unfold d1Base d1T
  exact repT_append (repT_append (repT_append aRep (repT_two zRep tRep)) cRep) dRep

theorem extOK_d1 : extOK d1T.length d1SlpA = true := by
  have h := d1_k
  unfold slpM at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

theorem repE : RepT 22 CFSG.Sporadic.Co2Cert.co2PackedVecs
    (CFSG.Sporadic.Co2Schreier.extendArrs (d1Base ()) d1SlpA) d1E :=
  repT_extend good V_size mmK_eq I22_eq _ repB extOK_d1

theorem stage_of {st : D1Stage} {P : ℕ → ℕ} (h : stageK st P = true) :
    d1StageOK (slpFinal (d1Base ()) d1SlpA) st = true := by
  unfold stageK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hi, ht⟩, hc⟩ := h
  have hS := repT_sel repE hi
  unfold d1StageOK
  rw [slpFinal_eq]
  exact slpTargets2_of hS (extP_eq_of_treeOK ht) (by rw [hS.1]; exact hc)

end CertificateChecks.Batch129080

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2 in
theorem certificate129080 : d1Check () = true := by
  unfold d1Check
  have hs : (d1Base ()).size = d1T.length := CertificateChecks.Batch129080.repB.1
  rw [Bool.and_eq_true]
  refine ⟨slpOK_of CertificateChecks.Batch129080.repB rfl (by rw [hs]; exact d1_k), ?_⟩
  simp only [Bool.and_eq_true]
  exact ⟨⟨CertificateChecks.Batch129080.stage_of d1_s1, CertificateChecks.Batch129080.stage_of d1_s2⟩, CertificateChecks.Batch129080.stage_of d1_s3⟩

end Certificates
