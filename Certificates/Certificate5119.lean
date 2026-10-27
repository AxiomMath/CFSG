module

public import CFSG.GH74.KGroups.L28TablesInputs
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.KGroupsE.K5119

public section

namespace Certificates

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L28 CFSG.Certificates.Kernel.PkEnum CertificateChecks.KernelKGroupsE

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.L28 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint in
theorem certificate5119 : (QS.check = true ∧ QS.orderCertificate = 8)
    ∧ (commCheck (elemsT QS) = true)
    ∧ (powInPCheck (elemsT QA) QP 8 = true)
    ∧ (leCheck QS QP = true) := by
  refine ⟨⟨check_certificate_of _ _ _ _ _ qs_5119K.1,
    (orderCertificate_eq_orderV _).trans qs_5119K.2⟩, ?_, ?_, ?_⟩
  · rw [elemsT_eq_elemsV]
    exact comm_5119K
  · rw [elemsT_eq_elemsV]
    simp only [powInPCheck, sift_eq_siftP]
    exact pow_5119K
  · simp only [leCheck, sift_eq_siftP]
    exact le_5119K

end Certificates
