module

public import CFSG.GH74.KGroups.M22Inputs
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.KGroupsE.K5127

public section

namespace Certificates

open CertificateChecks CFSG.Certificates.Kernel.PkEnum CertificateChecks.KernelKGroupsE

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.M22 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint in
set_option maxRecDepth 100000 in
theorem certificate5127 : (QP.check = true ∧ QP.orderCertificate = 443520)
    ∧ (QE.check = true ∧ QE.orderCertificate = 16)
    ∧ (sqOneCheck (elemsT QE) = true)
    ∧ (conjWordsCheck [m22gA, m22gB] eg0 cws (elemsT QE) = true)
    ∧ (indepCheck eg0 eg1 eg2 = true)
    ∧ (leCheck QE QP = true)
    ∧ (QE.sift eg0 0 = true)
    ∧ (QE.sift eg1 0 = true)
    ∧ (QE.sift eg2 0 = true) := by
  refine ⟨⟨check_certificate_of _ _ _ _ _ qp_5127K.1,
      (orderCertificate_eq_orderV _).trans qp_5127K.2⟩,
    ⟨check_certificate_of _ _ _ _ _ qe_5127K.1, (orderCertificate_eq_orderV _).trans qe_5127K.2⟩,
    ?_, ?_, indep_5127K, ?_, ?_, ?_, ?_⟩
  · rw [elemsT_eq_elemsV]
    exact sq_5127K
  · rw [elemsT_eq_elemsV]
    exact conj_5127K
  · simp only [leCheck, sift_eq_siftP]
    exact le_5127K
  · rw [sift_eq_siftP]
    exact sift_5127K.1
  · rw [sift_eq_siftP]
    exact sift_5127K.2.1
  · rw [sift_eq_siftP]
    exact sift_5127K.2.2

end Certificates
