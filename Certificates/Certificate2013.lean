
module

public import Certificates.Certificate2013Base

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Inputs
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA8Model
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallNoNilpCheck
import Certificates.Kernel.Census.CatFacts.C2013

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

theorem certificate2013 : (centTrivCheck (elemsT QS8) a8 b8 = true)
    ∧ (noNilpCheck (elemsT QS8) ((elemsT QA8).filter oddTest) 315 = true) := KernelCatFacts.facts2013

end Certificates
