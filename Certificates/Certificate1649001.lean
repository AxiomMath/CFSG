module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointInputs
import Certificates.Kernel.CosPres.F1649001
import Certificates.Kernel.CosPres.L1649001Glue
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.StandardType.QTwo.SixPoint

namespace Certificates

private theorem card4 : Finite (PG 10 (rels4 ())) ∧ Nat.card (PG 10 (rels4 ())) ≤ 25920 := by
  have h := TableFact.card_restrict (rels4 ()) (by norm_num) (subsetOf 10 [2, 3, 4, 5, 8, 9])
    (by decide) CFSG.KBFact.F1649001a1 CFSG.KBFact.F1649001a2
  exact ⟨h.1, h.2.trans (by norm_num)⟩

private theorem card5 : Finite (PG 14 (rels5 ())) ∧ Nat.card (PG 14 (rels5 ())) ≤ 528 * 25920 :=
  card_le_of_index_restrict (rels5 ()) (subsetOf 14 chart4)
    (TableFact.genSub_index (rels5 ()) (by norm_num) (subsetOf 14 chart4) CFSG.KBFact.F1649001b)
    card4

private theorem index5 :
    (genSub {r : FreeGroup (Fin 18) | r ∈ relsP.map FreeGroup.mk} (subsetOf 18 chart5)).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 18) | r ∈ relsP.map FreeGroup.mk} (subsetOf 18 chart5)).index =
        8064 := by
  obtain ⟨hfi, hle⟩ := TableFact.genSub_index relsP (by norm_num) (subsetOf 18 chart5)
    CFSG.KBFact.F1649001c
  exact ⟨hfi, le_antisymm hle (CFSG.KD.L1649001.index_chart5_ge_of_finiteIndex hfi)⟩

open CFSG.CosetTable CFSG.StandardType.QTwo.SixPoint in
theorem certificate1649001 :
    (Finite (PG 10 (rels4 ())) ∧ Nat.card (PG 10 (rels4 ())) ≤ 25920) ∧
      (Finite (PG 14 (rels5 ())) ∧ Nat.card (PG 14 (rels5 ())) ≤ 528 * 25920) ∧
      ((genSub {r : FreeGroup (Fin 18) | r ∈ relsP.map FreeGroup.mk} (subsetOf 18 chart5)).FiniteIndex ∧
        (genSub {r : FreeGroup (Fin 18) | r ∈ relsP.map FreeGroup.mk} (subsetOf 18 chart5)).index = 8064) :=
  ⟨card4, card5, index5⟩

end Certificates
