module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
public import CFSG.LocalAnalysis.WeakClosure81.SixFifteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (SwapsParabolics)
open CFSG.LocalAnalysis.WeakClosure81 (InFSq)

@[expose] def K_SwapSp4InF : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (L T : Subgroup Q) (n : ℕ),
    Fstar (⊤ : Subgroup Q) = L → IsSimpleGroup ↥L → IsSp4 ↥L n → 2 ≤ n →
      IsSylowIn 2 T ⊤ → L ⊔ T = ⊤ → SwapsParabolics T L → F12.InF n (⊤ : Subgroup Q)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
