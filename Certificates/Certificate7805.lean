module

public import CFSG.Milestones.ASVolI.F48.D43.Inputs3
import Certificates.Kernel.CosetCC.C7804
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG CFSG.ASVolI CFSG.CosetTable CFSG.KC.MiscCoset

namespace Certificates

private theorem certificate7805_rels_a :
    (burnsideF48d_Ws1 ()).map encW = CFSG.KBRoute.F7805a.rels := by
  decide +kernel

private theorem certificate7805_rels_b :
    (burnsideF48d_Ws2 ()).map encW = CFSG.KBRoute.F7805b.rels := by
  decide +kernel

private theorem certificate7805_rels_c :
    (burnsideF48d_Ws3 ()).map encW = CFSG.KBRoute.F7805c.rels := by
  decide +kernel

private theorem certificate7805_rels_d :
    (burnsideF48d_Ws4 ()).map encW = CFSG.KBRoute.F7805d.rels := by
  decide +kernel

open CFSG CFSG.ASVolI CFSG.CosetTable in
theorem certificate7805 : (Finite (PG _ (burnsideF48d_Ws3 ())) ∧ Nat.card (PG _ (burnsideF48d_Ws3 ())) ≤ 729 * 729) ∧
    (Finite (PG _ (burnsideF48d_Ws1 ())) ∧
      Nat.card (PG _ (burnsideF48d_Ws1 ())) ≤ 28 * (52 * (729 * 729))) := by
  have ha := CFSG.KBFact.F7805a
  have hb := CFSG.KBFact.F7805b
  have hc := CFSG.KBFact.F7805c
  have hd := CFSG.KBFact.F7805d
  rw [← certificate7805_rels_a] at ha
  rw [← certificate7805_rels_b] at hb
  rw [← certificate7805_rels_c] at hc
  rw [← certificate7805_rels_d] at hd
  have h3 := TableFact.card_restrict (burnsideF48d_Ws3 ()) (by decide)
    (subsetOf _ burnsideF48d_tSU2) (by decide) hc hd
  have h2 := card_le_of_index_restrict (burnsideF48d_Ws2 ()) (subsetOf _ burnsideF48d_tSU)
    (TableFact.genSub_index (burnsideF48d_Ws2 ()) (by decide) _ hb) h3
  have h1 := card_le_of_index_restrict (burnsideF48d_Ws1 ()) (subsetOf _ burnsideF48d_tSB)
    (TableFact.genSub_index (burnsideF48d_Ws1 ()) (by decide) _ ha) h2
  exact ⟨h3, h1⟩

end Certificates
