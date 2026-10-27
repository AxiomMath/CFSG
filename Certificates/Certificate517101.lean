module

public import Certificates.Data.S7SocL33
import CFSG.Certificates.Kernel.Census.CatFacts.LeCheck
import Certificates.Kernel.KGroupsE.K517101

public section

namespace Certificates

open CFSG.GH74.KGroups Certificates.S7SocL33 CFSG.Certificates.Kernel.PkEnum CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups Certificates.S7SocL33 in
theorem certificate517101 : (QSL.check = true ∧ QSL.orderCertificate = 32 ∧ leCheck QSL L33.QA = true) ∧
    l33SocCheck () = true := by
  refine ⟨⟨check_certificate_of _ _ _ _ _ qs_517101K.1,
    (orderCertificate_eq_orderV _).trans qs_517101K.2, ?_⟩, ?_⟩
  · rw [leCheck_eq_siftP]
    exact le_517101K
  · simp only [l33SocCheck, inQP, elemsT_eq_elemsV, sift_eq_siftP]
    exact soc_517101K

end Certificates
