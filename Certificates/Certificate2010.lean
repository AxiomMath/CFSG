module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallHeModelInputs
public meta import CFSG.Sporadic.HeldB.InnerRestrict
public meta import CFSG.Sporadic.HeldB.OuterCentRestrict
public meta import CFSG.GH74.KGroups.PermCheck
import Certificates.Kernel.Census.CatFacts.C2010

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall in
open CFSG.ComponentClassification.CatFactsSmall.He CFSG.GH74.KGroups CFSG.Certificates in
open CFSG.Sporadic.Schreier CFSG.Sporadic.HeldB Subgroup in
open CFSG.ComponentClassification.FixedCommutingProduct in
theorem certificate2010 : (QY0.check = true ∧ QY0.orderCertificate = 40320)
    ∧ (orderIs y00 5 = true ∧ orderIs y01 5 = true)
    ∧ (QYu.check = true ∧ QYu.orderCertificate = 1080)
    ∧ (orderIs yu0 5 = true ∧ orderIs yu1 5 = true) := KernelCatFacts.facts2010

end Certificates
