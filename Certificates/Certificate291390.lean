module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3DataTh
import Certificates.Kernel.ThU.Facts
import Certificates.Kernel.ThU.CoverA
import CFSG.Certificates.Kernel.ThU.CoverSound
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.CosetTable CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator CFSG.KC.MiscCoset

namespace Certificates

open CFSG.CosetTable CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator in
theorem certificate291390 : (∃ g : Fin 3 → (CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1 thULocal3.seedA
        thULocal3.seedB)ˣ,
      (∀ r ∈ thULocal3.rels, FreeGroup.lift g (FreeGroup.mk r) = 1) ∧
      (∀ i, g i ^ thULocal3.ords.getD i 0 = 1) ∧
      thULocal3.n ≤ Nat.card (Subgroup.closure (Set.range g))) ∧
    (Finite (PG 3 thUCover) ∧ Nat.card (PG 3 thUCover) ≤ thULocal3.n) :=
  ⟨CFSG.KD.ThU.thU_sub, CFSG.KC.ThU.card_thUCover_of
    (TableFact.card CFSG.KC.ThU.thUCoverW (by norm_num) CFSG.KBFact.ThUC)⟩

end Certificates
