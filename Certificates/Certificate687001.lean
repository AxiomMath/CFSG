module

public import Certificates.Data.Th687.GlueWords
public import CFSG.Certificates.CosetTableCompactColumns
import Certificates.Kernel.CosetCC.C687001
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

open CFSG.Sporadic.Th.Recog CFSG.CosetTable CFSG.KC.MiscCoset

namespace Certificates

local macro "collapse_unfold" : tactic => `(tactic|
  simp only [collapseRels, bfree, brel, R0', TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.Thompson.presentation, TauCeti.Sporadic.Thompson.relatorList,
    TauCeti.Sporadic.Thompson.relatorsOne, TauCeti.Sporadic.Thompson.relatorsTwo,
    TauCeti.Sporadic.Thompson.relatorsThree, TauCeti.Sporadic.Thompson.relatorsFour,
    TauCeti.Sporadic.Thompson.relatorsFive, TauCeti.Sporadic.Thompson.relatorsSix,
    TauCeti.Sporadic.Thompson.genA, TauCeti.Sporadic.Thompson.genB,
    TauCeti.Sporadic.Thompson.genC, TauCeti.Sporadic.Thompson.genD,
    TauCeti.Sporadic.Thompson.genE, TauCeti.Sporadic.Thompson.genS,
    TauCeti.Sporadic.Thompson.genT, TauCeti.Sporadic.Thompson.genU,
    TauCeti.Relator.toWord_gen, TauCeti.Relator.toWord_pow, TauCeti.Relator.toWord_mul,
    TauCeti.Relator.toWord_inv, TauCeti.Relator.toWord_div, TauCeti.Relator.toWord_conj,
    TauCeti.Relator.toWord_commInvInv, List.map_cons, List.map_append, List.map_nil])

private theorem certificate687001_rels_a :
    (collapseRels (.id, 1)).map encW = CFSG.KBRoute.F687001a.rels := by
  collapse_unfold
  decide +kernel

private theorem certificate687001_rels_b :
    (collapseRels (.f1, 0)).map encW = CFSG.KBRoute.F687001b.rels := by
  collapse_unfold
  decide +kernel

private theorem certificate687001_rels_c :
    (collapseRels (.f1, 1)).map encW = CFSG.KBRoute.F687001c.rels := by
  collapse_unfold
  decide +kernel

private theorem certificate687001_rels_d :
    (collapseRels (.f3, 0)).map encW = CFSG.KBRoute.F687001d.rels := by
  collapse_unfold
  decide +kernel

private theorem certificate687001_rels_e :
    (collapseRels (.f3, 1)).map encW = CFSG.KBRoute.F687001e.rels := by
  collapse_unfold
  decide +kernel

private theorem certificate687001_rels_f :
    (collapseRels (.f13, 0)).map encW = CFSG.KBRoute.F687001f.rels := by
  collapse_unfold
  decide +kernel

private theorem certificate687001_rels_g :
    (collapseRels (.f13, 1)).map encW = CFSG.KBRoute.F687001g.rels := by
  collapse_unfold
  decide +kernel

open CFSG.Sporadic.Th.Recog CFSG.CosetTable in
theorem certificate687001 : ∀ c : Config, c ≠ (.id, 0) →
    (genSub {r : FreeGroup (Fin 8) | r ∈ (collapseRels c).map FreeGroup.mk}
      (subsetOf 8 [0, 2, 3, 4, 5, 6, 7])).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin 8) | r ∈ (collapseRels c).map FreeGroup.mk}
      (subsetOf 8 [0, 2, 3, 4, 5, 6, 7])).index ≤ 1 := by
  have key : ∀ (c : Config) {rels : List (List (ℕ × Bool))}, (collapseRels c).map encW = rels →
      CFSG.Certificates.KB.TableFact 8 rels
        ((subsetOf 8 [0, 2, 3, 4, 5, 6, 7]).map fun x => [(x.val, true)]) 1 →
      (genSub {r : FreeGroup (Fin 8) | r ∈ (collapseRels c).map FreeGroup.mk}
        (subsetOf 8 [0, 2, 3, 4, 5, 6, 7])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 8) | r ∈ (collapseRels c).map FreeGroup.mk}
        (subsetOf 8 [0, 2, 3, 4, 5, 6, 7])).index ≤ 1 := by
    intro c rels hr h
    rw [← hr] at h
    exact TableFact.genSub_index (collapseRels c) (by norm_num) _ h
  rintro ⟨k, i⟩ hc
  cases k <;> fin_cases i
  · exact absurd rfl hc
  · exact key _ certificate687001_rels_a CFSG.KBFact.F687001a
  · exact key _ certificate687001_rels_b CFSG.KBFact.F687001b
  · exact key _ certificate687001_rels_c CFSG.KBFact.F687001c
  · exact key _ certificate687001_rels_d CFSG.KBFact.F687001d
  · exact key _ certificate687001_rels_e CFSG.KBFact.F687001e
  · exact key _ certificate687001_rels_f CFSG.KBFact.F687001f
  · exact key _ certificate687001_rels_g CFSG.KBFact.F687001g

end Certificates
