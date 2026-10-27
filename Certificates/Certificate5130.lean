module

public import CFSG.GH74.KGroups.Sz8TablesInputs
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.KGroupsE.K5130

public section

namespace Certificates

open CFSG.GH74.KGroups CFSG.GH74.KGroups.Sz8 CFSG.Certificates.Kernel.PkEnum CertificateChecks.KernelKGroupsE

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.Sz8 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint in
theorem certificate5130 : (QS.check = true ∧ QS.orderCertificate = 64)
    ∧ (benderCheck (elemsT QS) tt 7 = true)
    ∧ (((elemsT QS).filter (fun g => decide (centralIn (elemsT QS) g = true))).length = 8)
    ∧ (leCheck QS QP = true)
    ∧ (QP.sift tt 0 = true) := by
  refine ⟨⟨check_certificate_of _ _ _ _ _ qs_5130K.1,
    (orderCertificate_eq_orderV _).trans qs_5130K.2⟩, ?_, ?_, ?_, ?_⟩
  · rw [elemsT_eq_elemsV]
    exact bender_5130K
  · rw [elemsT_eq_elemsV]
    exact center_5130K
  · simp only [leCheck, sift_eq_siftP]
    exact le_5130K
  · rw [sift_eq_siftP]
    exact tt_5130K

end Certificates
