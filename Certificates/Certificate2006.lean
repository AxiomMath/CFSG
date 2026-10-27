
module

public import Certificates.Certificate2006Base

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA6Inputs
public meta import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.A6
import Certificates.Kernel.Census.CatFacts.C2006

public section

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall
open CFSG.ComponentClassification.CatFactsSmall.A6 CFSG.GH74.KGroups CFSG.GH74.KGroups.A6
open CFSG.Certificates CFSG.Sporadic.Schreier Subgroup CFSG.ComponentClassification.GSThmB

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall in
open CFSG.ComponentClassification.CatFactsSmall.A6 CFSG.GH74.KGroups CFSG.GH74.KGroups.A6 in
open CFSG.Certificates CFSG.Sporadic.Schreier Subgroup CFSG.ComponentClassification.GSThmB in

theorem certificate2006 : (expCheck (elemsT QA) = true)
    ∧ (diagCheck (elemsT QA) (elemsT QP) = true)
    ∧ (innerCheck (elemsT QA) (elemsT QP) = true)
    ∧ (noCommCheck (elemsT QA) (elemsT QP) = true) := KernelCatFacts.facts2006

end Certificates
