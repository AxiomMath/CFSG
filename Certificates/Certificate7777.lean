module

public import CFSG.Milestones.ASVolI.F48.Rest.U52eInputs
public import CFSG.Certificates.Kernel.Misc.Coset.PG
import Certificates.Kernel.PresLetters.F7777
import Certificates.Kernel.PresLetters.F7771A
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.LieType.BorelTits.CompleteFlag
public import Certificates.Data.Kernel.Bounds.TableFact

public section

open CFSG CFSG.ASVolI CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Certificates

namespace CertificateChecks.PresLetters7777

#kc_forall_chunks idx (fun k => KB.TableFact 5
  ((burnsideF48t_u52eWs (burnsideF48t_u52eCands.getD k (0, 0, 0, 0)).1
    (burnsideF48t_u52eCands.getD k (0, 0, 0, 0)).2.1
    (burnsideF48t_u52eCands.getD k (0, 0, 0, 0)).2.2.1).map encW)
  ((subsetOf 5 [0, 1, 2, 4]).map fun x => [(x.val, true)])
  (burnsideF48t_u52eCands.getD k (0, 0, 0, 0)).2.2.2) 30 CFSG.KBFact.F7777a 1

theorem restrict : ∀ k < 30, restrictWords (subsetOf 5 [0, 1, 2, 4])
    (burnsideF48t_u52eWs (burnsideF48t_u52eCands.getD k (0, 0, 0, 0)).1
      (burnsideF48t_u52eCands.getD k (0, 0, 0, 0)).2.1
      (burnsideF48t_u52eCands.getD k (0, 0, 0, 0)).2.2.1) = burnsideF48t_u52eWsB := by
  decide +kernel

theorem wsBB : burnsideF48t_u52eWsBB.map encW = burnsideF48t_u52WsB.map encW := by
  decide +kernel

theorem cardB : Finite (PG (subsetOf 5 [0, 1, 2, 4]).length burnsideF48t_u52eWsB) ∧
    Nat.card (PG (subsetOf 5 [0, 1, 2, 4]).length burnsideF48t_u52eWsB) ≤ 2 * 82944 := by
  have hb : KB.TableFact (subsetOf (subsetOf 5 [0, 1, 2, 4]).length [0, 1, 2]).length
      (burnsideF48t_u52WsB.map encW) [] 82944 := CFSG.KBFact.F7771b
  rw [← wsBB] at hb
  exact TableFact.card_restrict _ (by decide) (subsetOf (subsetOf 5 [0, 1, 2, 4]).length [0, 1, 2])
    (by decide) CFSG.KBFact.F7777b hb

end CertificateChecks.PresLetters7777

namespace Certificates

open CertificateChecks.PresLetters7777 in
open CFSG CFSG.ASVolI CFSG.CosetTable in
theorem certificate7777 : ∀ t ∈ burnsideF48t_u52eCands, Finite (PG 5 (burnsideF48t_u52eWs t.1 t.2.1 t.2.2.1)) ∧
    Nat.card (PG 5 (burnsideF48t_u52eWs t.1 t.2.1 t.2.2.1)) ≤ t.2.2.2 * 165888 := fun t ht => by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ht
  have hl : burnsideF48t_u52eCands.length = 30 := rfl
  have hk' : k < 30 := hl ▸ hk
  rw [← List.getD_eq_getElem _ (0, 0, 0, 0) hk]
  have hr := cardB
  rw [← restrict k hk'] at hr
  obtain ⟨f, c⟩ := card_le_of_index_restrict _ (subsetOf 5 [0, 1, 2, 4])
    (TableFact.genSub_index _ (by norm_num) _ (idx k hk')) hr
  exact ⟨f, c.trans (by norm_num)⟩

end Certificates
