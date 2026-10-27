module

public import Certificates.Data.PSp43Sylow
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.SchreierFam.C23100K

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.Certificates.Kernel.PkEnum

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Certificates in
theorem certificate23100 : (QT0.check = true ∧ QT0.orderCertificate = 64) ∧ centInvT0.length = 1 := by
  refine ⟨⟨check_certificate_of _ _ _ _ _ KernelSchreierFam.qt0_23100K.1,
    (orderCertificate_eq_orderV _).trans KernelSchreierFam.qt0_23100K.2⟩, ?_⟩
  unfold centInvT0 invT0
  rw [elemsT_eq_elemsV]
  exact KernelSchreierFam.cent_23100K

end Certificates
