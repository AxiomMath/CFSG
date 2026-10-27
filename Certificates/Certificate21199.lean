module

public import CFSG.CGT.A8S.A8EnumInputs
public import CFSG.CGT.A8S.CollapseInputs
import Certificates.Kernel.PresLetters.F21199
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Data.Kernel.Bounds.TableFact
public import Mathlib

public section

open CFSG.CGT.A8S CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Certificates

namespace CertificateChecks.PresLetters21199

#kc_forall_chunks coll (fun k => KB.TableFact 6
  ((collRelsA8 ⟨k % 7, Nat.mod_lt _ (by norm_num)⟩).map encW)
  ((subsetOf 6 (List.range 5)).map fun x => [(x.val, true)]) 1) 7 CFSG.KBFact.F21199c 1

end CertificateChecks.PresLetters21199

namespace Certificates

open CertificateChecks.PresLetters21199 in
open CFSG.CGT.A8S CFSG.CosetTable in
theorem certificate21199 : ((genSub {r : FreeGroup (Fin 6) | r ∈ a8Rels.map FreeGroup.mk}
        (subsetOf 6 (List.range 5))).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 6) | r ∈ a8Rels.map FreeGroup.mk}
        (subsetOf 6 (List.range 5))).index ≤ 15) ∧
    ∀ k : Fin 7, (genSub {r : FreeGroup (Fin 6) | r ∈ (collRelsA8 k).map FreeGroup.mk}
        (subsetOf 6 (List.range 5))).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 6) | r ∈ (collRelsA8 k).map FreeGroup.mk}
        (subsetOf 6 (List.range 5))).index ≤ 1 :=
  ⟨TableFact.genSub_index a8Rels (by norm_num) (subsetOf 6 (List.range 5)) CFSG.KBFact.F21199a,
    fun k => TableFact.genSub_index (collRelsA8 k) (by norm_num) (subsetOf 6 (List.range 5)) (by
      have h := coll k.val k.isLt
      rwa [show (⟨k.val % 7, Nat.mod_lt _ (by norm_num)⟩ : Fin 7) = k from
        Fin.ext (Nat.mod_eq_of_lt k.isLt)] at h)⟩

end Certificates
