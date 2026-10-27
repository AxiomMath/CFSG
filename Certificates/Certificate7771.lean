module

public import CFSG.Milestones.ASVolI.F48.Rest.U52Inputs
import Certificates.Kernel.PresLetters.F7771
import Certificates.Kernel.PresLetters.F7771A
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.LieType.BorelTits.CompleteFlag
public import Certificates.Data.Kernel.Bounds.TableFact

public section

open CFSG CFSG.ASVolI CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Certificates

namespace CertificateChecks.PresLetters7771

#kc_forall_chunks idx (fun k => KB.TableFact 4
  ((burnsideF48t_u52Ws (burnsideF48t_u52Cands.getD k (0, 0, 0, 0)).1
    (burnsideF48t_u52Cands.getD k (0, 0, 0, 0)).2.1
    (burnsideF48t_u52Cands.getD k (0, 0, 0, 0)).2.2.1).map encW)
  ((subsetOf 4 [0, 1, 2]).map fun x => [(x.val, true)])
  (burnsideF48t_u52Cands.getD k (0, 0, 0, 0)).2.2.2) 24 CFSG.KBFact.F7771a 1

theorem restrict : ∀ k < 24, restrictWords (subsetOf 4 [0, 1, 2])
    (burnsideF48t_u52Ws (burnsideF48t_u52Cands.getD k (0, 0, 0, 0)).1
      (burnsideF48t_u52Cands.getD k (0, 0, 0, 0)).2.1
      (burnsideF48t_u52Cands.getD k (0, 0, 0, 0)).2.2.1) = burnsideF48t_u52WsB := by
  decide +kernel

end CertificateChecks.PresLetters7771

namespace Certificates

open CertificateChecks.PresLetters7771 in
open CFSG CFSG.ASVolI CFSG.CosetTable in
theorem certificate7771 : ∀ t ∈ burnsideF48t_u52Cands, Finite (PG 4 (burnsideF48t_u52Ws t.1 t.2.1 t.2.2.1)) ∧
    Nat.card (PG 4 (burnsideF48t_u52Ws t.1 t.2.1 t.2.2.1)) ≤ t.2.2.2 * 82944 := fun t ht => by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ht
  have hl : burnsideF48t_u52Cands.length = 24 := rfl
  have hk' : k < 24 := hl ▸ hk
  rw [← List.getD_eq_getElem _ (0, 0, 0, 0) hk]
  have hb : KB.TableFact (subsetOf 4 [0, 1, 2]).length (burnsideF48t_u52WsB.map encW) [] 82944 :=
    CFSG.KBFact.F7771b
  rw [← restrict k hk'] at hb
  exact TableFact.card_restrict _ (by norm_num) (subsetOf 4 [0, 1, 2]) (by decide) (idx k hk') hb

end Certificates
