module

public import CFSG.Milestones.ASVolI.F48.D43.EInputs
import Certificates.Kernel.CosetCC.C7813
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Misc.Coset.PGNormal
public import Certificates.Certificate113

public section

open CFSG CFSG.ASVolI CFSG.CosetTable CFSG.KC.MiscCoset

namespace Certificates

private def certificate7813_F : Fin (subsetOf 18 burnsideF48dE_S1).length := ⟨1, by decide⟩

private def certificate7813_A : List (Fin (subsetOf 18 burnsideF48dE_S1).length) :=
  subsetOf (subsetOf 18 burnsideF48dE_S1).length
    [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]

private theorem certificate7813_rels1 :
    (burnsideF48dE_Ws 1).map encW = CFSG.KBRoute.F7813e1.rels := by
  decide +kernel

private theorem certificate7813_rels2 :
    (burnsideF48dE_Ws 2).map encW = CFSG.KBRoute.F7813e2.rels := by
  decide +kernel

private theorem certificate7813_all : ∀ j : Fin (subsetOf 18 burnsideF48dE_S1).length,
    j ∈ certificate7813_A ∨ j = certificate7813_F := by
  decide +kernel

private theorem certificate7813_conj : ∀ a ∈ certificate7813_A,
    burnsideF48dE_WsP1.any (conjOK certificate7813_A certificate7813_F a) = true := by
  decide +kernel

private theorem certificate7813_cube :
    List.replicate 3 (certificate7813_F, true) ∈ burnsideF48dE_WsP1 := by
  decide +kernel

open CFSG CFSG.ASVolI CFSG.CosetTable in
theorem certificate7813 : ((genSub {r : FreeGroup (Fin 18) | r ∈ (burnsideF48dE_Ws 1).map FreeGroup.mk}
        (subsetOf 18 burnsideF48dE_S1)).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 18) | r ∈ (burnsideF48dE_Ws 1).map FreeGroup.mk}
        (subsetOf 18 burnsideF48dE_S1)).index ≤ 1) ∧
    ((genSub {r : FreeGroup (Fin 18) | r ∈ (burnsideF48dE_Ws 2).map FreeGroup.mk}
        (subsetOf 18 burnsideF48dE_S1)).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 18) | r ∈ (burnsideF48dE_Ws 2).map FreeGroup.mk}
        (subsetOf 18 burnsideF48dE_S1)).index ≤ 1) ∧
    ((genSub {r : FreeGroup (Fin (subsetOf 18 burnsideF48dE_S1).length) |
          r ∈ burnsideF48dE_WsP1.map FreeGroup.mk}
        (subsetOf (subsetOf 18 burnsideF48dE_S1).length
          [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin (subsetOf 18 burnsideF48dE_S1).length) |
          r ∈ burnsideF48dE_WsP1.map FreeGroup.mk}
        (subsetOf (subsetOf 18 burnsideF48dE_S1).length
          [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16])).index ≤ 3) := by
  have h1 := CFSG.KBFact.F7813e1
  have h2 := CFSG.KBFact.F7813e2
  rw [← certificate7813_rels1] at h1
  rw [← certificate7813_rels2] at h2
  exact ⟨TableFact.genSub_index (burnsideF48dE_Ws 1) (by norm_num) _ h1,
    TableFact.genSub_index (burnsideF48dE_Ws 2) (by norm_num) _ h2,
    genSub_index_le_of_normal certificate7813_all certificate7813_conj (by norm_num)
      certificate7813_cube⟩

end Certificates
