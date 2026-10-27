module

public import CFSG.GH74.KGroups.U33TablesInputs
import CFSG.Certificates.Kernel.Census.CatFacts.LeCheck
import Certificates.Kernel.KGroupsE.K5134

public section

namespace Certificates

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Certificates.Kernel.PkEnum CertificateChecks.KernelKGroupsE

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.U33 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint in
theorem certificate5134 : (QS.check = true ∧ QS.orderCertificate = 32)
    ∧ (invConjCheck (elemsT QP) t0 = true)
    ∧ (smallCheck (elemsT QS) s0 = true)
    ∧ (leCheck QS QP = true) := by
  refine ⟨⟨check_certificate_of _ _ _ _ _ qs_5134K.1,
    (orderCertificate_eq_orderV _).trans qs_5134K.2⟩, ?_, ?_, ?_⟩
  · rw [elemsT_eq_elemsV]
    exact inv_5134K
  · rw [elemsT_eq_elemsV]
    exact small_5134K
  · rw [leCheck_eq_siftP]
    exact le_5134K

end Certificates
