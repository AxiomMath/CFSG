
module

public import Certificates.Certificate2014Base

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8DataInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Gen
public meta import CFSG.GH74.KGroups.Checks3
import Certificates.Kernel.Census.CatFacts.C2014

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

theorem certificate2014 : (admCheck (elemsT QS8) QA8 five8 s8 admConj = true)
    ∧ (QL8.check = true ∧ QL8.orderCertificate = 360)
    ∧ (oddNormalCheck (elemsT QL8) 45 = true)
    ∧ (((elemsT QA8).filter (fun g => decide (g * s8 = s8 * g))).length = 720)
    ∧ (QQ8.check = true ∧ QQ8.orderCertificate = 32)
    ∧ ((elemsT QQ8).all (fun q => QQ8.sift (g08 * q * g08⁻¹) 0) = true ∧
      QQ8.sift g08 0 = false ∧ QQ8.sift (g08 * g08) 0 = true
    )
    ∧ (((elemsT QS8).filter (fun g => decide (g * s8 = s8 * g))).length = 2 ^ 5 * 45) := KernelCatFacts.facts2014

end Certificates
