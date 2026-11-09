module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24ThreeCoverInputs
import Certificates.Kernel.Misc.Coset.Q3Act.TzIndex
import Certificates.Kernel.Misc.Coset.Q3Act.Facts

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
  exact CFSG.KAct.Q3.genSub_index_tz12 CFSG.KAct.Q3.genSub_index_tz12_le

end Certificates
