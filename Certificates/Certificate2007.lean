
module

public import Certificates.Certificate2007Base

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA8ModelInputs
public meta import CFSG.GH74.KGroups.Checks
import Certificates.Kernel.Census.CatFacts.C2007

public section

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall
open CFSG.ComponentClassification.CatFactsSmall.A8 CFSG.GH74.KGroups CFSG.Certificates
open CFSG.Sporadic.Schreier Subgroup

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall in
open CFSG.ComponentClassification.CatFactsSmall.A8 CFSG.GH74.KGroups CFSG.Certificates in
open CFSG.Sporadic.Schreier Subgroup in

theorem certificate2007 : (QS8.check = true ∧ QS8.orderCertificate = 40320)
    ∧ (QA8.check = true ∧ QA8.orderCertificate = 20160) := KernelCatFacts.facts2007

end Certificates
