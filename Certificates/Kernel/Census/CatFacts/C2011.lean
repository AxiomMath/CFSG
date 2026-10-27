
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34RankInputs
public meta import CFSG.GH74.KGroups.Checks3
public meta import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.Census.CatFacts.C2011K

public section

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall.L34 CFSG.ComponentClassification.PSL3Four
  CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum

open Certificates in
open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall in
open CFSG.ComponentClassification.CatFactsSmall.L34 CFSG.GH74.KGroups CFSG.Certificates in
open CFSG.Sporadic.Schreier Subgroup CFSG.ComponentClassification.GSThmB in
open CFSG.ComponentClassification.PSL3Four in
theorem facts2011 : (QS.check = true ∧ QS.orderCertificate = 20160)
    ∧ (QE.check = true ∧ QE.orderCertificate = 16)
    ∧ (classCheck (elemsT QS) g₂ conjugators = true)
    ∧ (sqOneCheck (elemsT QE) = true)
    ∧ (indepCheck g₂ g₃ c₁ = true) :=
  ⟨⟨check_certificate_of _ _ _ _ _ qs_2011K.1, (orderCertificate_eq_orderV _).trans qs_2011K.2⟩,
    ⟨check_certificate_of _ _ _ _ _ qe_2011K.1, (orderCertificate_eq_orderV _).trans qe_2011K.2⟩,
    by rw [elemsT_eq_elemsV]; exact class_2011K, by rw [elemsT_eq_elemsV]; exact sq_2011K.1,
    sq_2011K.2⟩

end CertificateChecks.KernelCatFacts
