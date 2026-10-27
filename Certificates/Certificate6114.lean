module

public import CFSG.Sporadic.Recognition.LyonsFinalBInputs
import Certificates.Kernel.CosetCC.C6114A
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import Mathlib.Algebra.Order.Ring.Star

public section

open CFSG.Sporadic.Recognition.LyonsSims.LyFinal CFSG.CosetTable CFSG.KC.MiscCoset

namespace Certificates

private theorem certificate6114_rels_a : RB5.map encW = CFSG.KBRoute.F6114a.rels := by
  decide +kernel

private theorem certificate6114_rels_b : RB4.map encW = CFSG.KBRoute.F6114b.rels := by
  decide +kernel

private theorem certificate6114_rels_c : RB3.map encW = CFSG.KBRoute.F6114c.rels := by
  decide +kernel

private theorem certificate6114_rels_d : RB2.map encW = CFSG.KBRoute.F6114d.rels := by
  decide +kernel

open CFSG.Sporadic.Recognition.LyonsSims.LyFinal CFSG.CosetTable in
theorem certificate6114 : Finite (PG _ RB5) ∧ Nat.card (PG _ RB5) ≤ 5388768000 := by
  have ha := CFSG.KBFact.F6114a
  have hb := CFSG.KBFact.F6114b
  have hc := CFSG.KBFact.F6114c
  have hd := CFSG.KBFact.F6114d
  rw [← certificate6114_rels_a] at ha
  rw [← certificate6114_rels_b] at hb
  rw [← certificate6114_rels_c] at hc
  rw [← certificate6114_rels_d] at hd
  have h3 := TableFact.card_restrict RB3 (by decide) (subsetOf _ [0]) (by decide) hc hd
  have h2 := card_le_of_index_restrict RB4 (subsetOf _ [1, 2])
    (TableFact.genSub_index RB4 (by decide) _ hb) h3
  have h1 := card_le_of_index_restrict RB5 (subsetOf _ [2, 3, 4])
    (TableFact.genSub_index RB5 (by decide) _ ha) h2
  exact ⟨h1.1, h1.2.trans (by norm_num)⟩

end Certificates
