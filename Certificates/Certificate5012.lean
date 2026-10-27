module

public import CFSG.GH74.E2.L33OuterTablesInputs
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.SchreierFam.C5012K

public section

namespace Certificates

open CertificateChecks

open CFSG.GH74.E2 CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.E2 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups in
theorem certificate5012 : (outerConjCheck L33.QP (elemsT L33.QA) = true)
    ∧ (outerCommCheck L33.QP (elemsT L33.QA) (elemsT L33.QP) = true) := by
  rw [elemsT_eq_elemsV, elemsT_eq_elemsV]
  exact ⟨KernelSchreierFam.conj_5012K, KernelSchreierFam.comm_5012K⟩

end Certificates
