module

public import Certificates.Data.Th687.DModel
public import CFSG.Sporadic.Th.Recog.JLettersInputs
public import Certificates.Data.CFSGNative.ONSchreier.Compact
import Certificates.Kernel.CosetCC.C687005
import Certificates.Kernel.Th.DModel.Glue
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.Sporadic.Th.Recog CFSG.CosetTable CFSG.KC.MiscCoset

namespace Certificates

private theorem certificate687005_rels :
    RD.map encW = CFSG.KBRoute.F687005.rels := by
  rw [CertificateChecks.KernelTh.DModel.RD_eq]
  decide +kernel

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 in
open CFSG.Sporadic.Th.Recog CFSG.CosetTable CFSG.PSL3Four.Native in
theorem certificate687005 :
    (Finite (PG 6 RD) ∧ Nat.card (PG 6 RD) ≤ 3456) ∧
      eqRows (prodRows (List.replicate 6 (mulRows (rowsHsw 3) (rowsHsw 7)))) CFSG.Sporadic.Th.Native.idRows = true ∧
      (∀ j : Fin 6,
        CFSG.ONSchreier.Native.pisInv 51 letArr[j.val]! (letInv ())[j.val]! = true) ∧
      invsOK 51 letArr (letInv ()) = true ∧
      rdCheck () = true ∧
      tConjCheck () = true ∧
      enumOK 51 letArr (dEnum ()) = true ∧
      (dEnum ()).tabs.size = 3456 ∧
      kerCheck () = true ∧
      (sqTabs ()).length = 164 := by
  have h := CFSG.KBFact.F687005
  rw [← certificate687005_rels] at h
  exact ⟨TableFact.card RD (by norm_num) h, CertificateChecks.KernelTh.DModel.dModel_true⟩

end Certificates
