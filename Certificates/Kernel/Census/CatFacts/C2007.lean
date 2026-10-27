
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA8ModelInputs
public meta import CFSG.GH74.KGroups.Checks
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.Census.CatFacts.C2007K

public section

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall.A8 CFSG.Certificates.Kernel.PkEnum

open Certificates in
open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall in
open CFSG.ComponentClassification.CatFactsSmall.A8 CFSG.GH74.KGroups CFSG.Certificates in
open CFSG.Sporadic.Schreier Subgroup in
theorem facts2007 : (QS8.check = true ∧ QS8.orderCertificate = 40320)
    ∧ (QA8.check = true ∧ QA8.orderCertificate = 20160) :=
  ⟨⟨check_certificate_of _ _ _ _ _ qs8_2007K.1,
      (orderCertificate_eq_orderV _).trans qs8_2007K.2⟩,
    ⟨check_certificate_of _ _ _ _ _ qa8_2007K.1,
      (orderCertificate_eq_orderV _).trans qa8_2007K.2⟩⟩

end CertificateChecks.KernelCatFacts
