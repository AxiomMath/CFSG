module

public import Certificates.Data.Th687.SplitT
import Certificates.Kernel.CosetCC.C687004A
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.Sporadic.Th.Recog CFSG.CosetTable CFSG.KC.MiscCoset

namespace Certificates

private theorem certificate687004_rels_a :
    (Tc ((0, 1) : Fin 3 × Fin 3)).map encW = CFSG.KBRoute.F687004a.rels := by decide +kernel

private theorem certificate687004_rels_b :
    (Tc ((0, 2) : Fin 3 × Fin 3)).map encW = CFSG.KBRoute.F687004b.rels := by decide +kernel

private theorem certificate687004_rels_c :
    (Tc ((1, 0) : Fin 3 × Fin 3)).map encW = CFSG.KBRoute.F687004c.rels := by decide +kernel

private theorem certificate687004_rels_d :
    (Tc ((1, 1) : Fin 3 × Fin 3)).map encW = CFSG.KBRoute.F687004d.rels := by decide +kernel

private theorem certificate687004_rels_e :
    (Tc ((1, 2) : Fin 3 × Fin 3)).map encW = CFSG.KBRoute.F687004e.rels := by decide +kernel

private theorem certificate687004_rels_f :
    (Tc ((2, 0) : Fin 3 × Fin 3)).map encW = CFSG.KBRoute.F687004f.rels := by decide +kernel

private theorem certificate687004_rels_g :
    (Tc ((2, 1) : Fin 3 × Fin 3)).map encW = CFSG.KBRoute.F687004g.rels := by decide +kernel

private theorem certificate687004_rels_h :
    (Tc ((2, 2) : Fin 3 × Fin 3)).map encW = CFSG.KBRoute.F687004h.rels := by decide +kernel

open CFSG.Sporadic.Th.Recog CFSG.CosetTable in
theorem certificate687004 : ∀ c : Fin 3 × Fin 3, c ≠ (0, 0) →
    (genSub {r : FreeGroup (Fin 7) | r ∈ (Tc c).map FreeGroup.mk}
      (subsetOf 7 [0, 1, 2, 3, 4])).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin 7) | r ∈ (Tc c).map FreeGroup.mk}
      (subsetOf 7 [0, 1, 2, 3, 4])).index ≤ 7371 := by
  have key : ∀ (c : Fin 3 × Fin 3) {rels : List (List (ℕ × Bool))}, (Tc c).map encW = rels →
      CFSG.Certificates.KB.TableFact 7 rels
        ((subsetOf 7 [0, 1, 2, 3, 4]).map fun x => [(x.val, true)]) 7371 →
      (genSub {r : FreeGroup (Fin 7) | r ∈ (Tc c).map FreeGroup.mk}
        (subsetOf 7 [0, 1, 2, 3, 4])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 7) | r ∈ (Tc c).map FreeGroup.mk}
        (subsetOf 7 [0, 1, 2, 3, 4])).index ≤ 7371 := by
    intro c rels hr h
    rw [← hr] at h
    exact TableFact.genSub_index (Tc c) (by norm_num) _ h
  rintro ⟨c1, c2⟩ hc
  fin_cases c1 <;> fin_cases c2
  · exact absurd rfl hc
  · exact key _ certificate687004_rels_a CFSG.KBFact.F687004a
  · exact key _ certificate687004_rels_b CFSG.KBFact.F687004b
  · exact key _ certificate687004_rels_c CFSG.KBFact.F687004c
  · exact key _ certificate687004_rels_d CFSG.KBFact.F687004d
  · exact key _ certificate687004_rels_e CFSG.KBFact.F687004e
  · exact key _ certificate687004_rels_f CFSG.KBFact.F687004f
  · exact key _ certificate687004_rels_g CFSG.KBFact.F687004g
  · exact key _ certificate687004_rels_h CFSG.KBFact.F687004h

end Certificates
