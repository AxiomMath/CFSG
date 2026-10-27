module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24ThreeCoverInputs
import Certificates.Kernel.CosPres.F291372A
import Certificates.Kernel.Misc.Coset.Q3Act.Facts
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.CosetTable CFSG.Sporadic.Recognition.Fi24PrimeMultiplier
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

namespace Certificates

open CFSG.CosetTable CFSG.Sporadic.Presentation.Fi24Prime
  CFSG.Sporadic.Recognition.Fi24PrimeMultiplier
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator in
theorem certificate291372 :
    ((X0.getD sqIdx []).map (fun l => (l.1.val, l.2)) = [(8, true), (8, true)]) ∧
    ((genSub {r : FreeGroup (Fin nG) | r ∈ wsQ.map FreeGroup.mk} (subsetOf nG S0)).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin nG) | r ∈ wsQ.map FreeGroup.mk} (subsetOf nG S0)).index ≤
        920808) ∧
    3 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin nG) | r ∈ wsQ.map FreeGroup.mk}
      (FreeGroup.mk (zetaWord 10))) := by
  refine ⟨CFSG.KAct.Q3.sq_letters, ?_, CFSG.KAct.Q3.three_dvd_orderOf_zeta⟩
  rw [CFSG.KAct.Q3.wsQ_eq]
  exact CFSG.KC.MiscCoset.TableFact.genSub_index (CFSG.KAct.Q3.wsQN CFSG.KD.OrdFi24p.rels)
    (by norm_num) (subsetOf nG S0) CFSG.KBFact.F291372a

end Certificates
