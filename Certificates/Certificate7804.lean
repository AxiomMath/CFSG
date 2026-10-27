module

public import CFSG.Milestones.ASVolI.F48.D43.Inputs3
import Certificates.Kernel.CosetCC.C7804
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import Mathlib.Algebra.Order.Ring.Star

public section

open CFSG CFSG.ASVolI CFSG.CosetTable CFSG.KC.MiscCoset

namespace Certificates

private theorem certificate7804_rels_eq :
    (burnsideF48d_Ws ()).map encW = CFSG.KBRoute.F7804.rels := by
  decide +kernel

open CFSG CFSG.ASVolI CFSG.CosetTable in
theorem certificate7804 : (genSub {r : FreeGroup (Fin 17) | r ∈ (burnsideF48d_Ws ()).map FreeGroup.mk}
      (subsetOf 17 burnsideF48d_tS1)).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin 17) | r ∈ (burnsideF48d_Ws ()).map FreeGroup.mk}
      (subsetOf 17 burnsideF48d_tS1)).index ≤ 26572 := by
  have h := CFSG.KBFact.F7804
  rw [← certificate7804_rels_eq] at h
  exact TableFact.genSub_index (burnsideF48d_Ws ()) (by norm_num) (subsetOf 17 burnsideF48d_tS1) h

end Certificates
