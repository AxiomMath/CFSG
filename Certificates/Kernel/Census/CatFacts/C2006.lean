
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA6Inputs
public meta import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.A6
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.Census.CatFacts.C2006K

public section

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall.A6 CFSG.GH74.KGroups CFSG.GH74.KGroups.A6
  CFSG.Certificates.Kernel.PkEnum

open Certificates in
open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall in
open CFSG.ComponentClassification.CatFactsSmall.A6 CFSG.GH74.KGroups CFSG.GH74.KGroups.A6 in
open CFSG.Certificates CFSG.Sporadic.Schreier Subgroup CFSG.ComponentClassification.GSThmB in
theorem facts2006 : (expCheck (elemsT QA) = true)
    ∧ (diagCheck (elemsT QA) (elemsT QP) = true)
    ∧ (innerCheck (elemsT QA) (elemsT QP) = true)
    ∧ (noCommCheck (elemsT QA) (elemsT QP) = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [elemsT_eq_elemsV]
  · exact exp2006K
  · rw [elemsT_eq_elemsV]
    exact diag2006K
  · rw [elemsT_eq_elemsV]
    exact inner2006K
  · rw [elemsT_eq_elemsV]
    exact noComm2006K

end CertificateChecks.KernelCatFacts
