
module

public import Certificates.Certificate2019Base

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81A8PermInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Data
import Certificates.Kernel.Census.CatFacts.C2019

public section

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.GSThmB
open CFSG.ComponentClassification.GSThmB.A8 CFSG.GH74.KGroups CFSG.Certificates
open CFSG.Sporadic.Schreier Subgroup CFSG.ComponentClassification.CatFactsSmall.A8

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.GSThmB in
open CFSG.ComponentClassification.GSThmB.A8 CFSG.GH74.KGroups CFSG.Certificates in
open CFSG.Sporadic.Schreier Subgroup CFSG.ComponentClassification.CatFactsSmall.A8 in

theorem certificate2019 : (tauCheck (elemsT QA8) t15 = true)
    ∧ (n3Check (elemsT QL8) QL8 n3Data = true)
    ∧ (n4Check (elemsT QS8) (elemsT QA8) t15 = true) := KernelCatFacts.facts2019

end Certificates
