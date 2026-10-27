module

public import CFSG.GH74.AS16.E2.Local3ChecksInputs
public import CFSG.GH74.KGroups.M11TablesInputs
public import CFSG.GH74.KGroups.L33TablesInputs
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.KGroupsE.K5000

public section

namespace Certificates

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum CertificateChecks.KernelKGroupsE

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.AS16 in
open CFSG.GH74.AS16.E2 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.GH74.KGroups in
theorem certificate5000 : (local3Check (elemsT M11.Q) M11.t0 = true)
    ∧ (expCheck (elemsT M11.Q) 27 3 = true)
    ∧ (local3Check (elemsT L33.QP) L33.t0 = true)
    ∧ (expCheck (elemsT L33.QP) 27 3 = true) := by
  simp only [elemsT_eq_elemsV]
  exact ⟨m11_local3_5000K, m11_exp_5000K, l33_local3_5000K, l33_exp_5000K⟩

end Certificates
