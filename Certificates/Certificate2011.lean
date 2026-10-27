
module

public import Certificates.Certificate2011Base

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34RankInputs
public meta import CFSG.GH74.KGroups.Checks3
public meta import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import Certificates.Kernel.Census.CatFacts.C2011

public section

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall
open CFSG.ComponentClassification.CatFactsSmall.L34 CFSG.GH74.KGroups CFSG.Certificates
open CFSG.Sporadic.Schreier Subgroup CFSG.ComponentClassification.GSThmB
open CFSG.ComponentClassification.PSL3Four

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall in
open CFSG.ComponentClassification.CatFactsSmall.L34 CFSG.GH74.KGroups CFSG.Certificates in
open CFSG.Sporadic.Schreier Subgroup CFSG.ComponentClassification.GSThmB in
open CFSG.ComponentClassification.PSL3Four in

theorem certificate2011 : (QS.check = true ∧ QS.orderCertificate = 20160)
    ∧ (QE.check = true ∧ QE.orderCertificate = 16)
    ∧ (classCheck (elemsT QS) g₂ conjugators = true)
    ∧ (sqOneCheck (elemsT QE) = true)
    ∧ (indepCheck g₂ g₃ c₁ = true) := KernelCatFacts.facts2011

end Certificates
