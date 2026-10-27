module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

@[expose] def K_U3IndexNormal : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K T H : Subgroup X) (n : ℕ),
    K ≤ H → (K.subgroupOf H).Normal → ⁅K, K⁆ = K →
    CFSG.Open.IsQuasisimple (Bar2 K) → IsSU3 (Bar2 K) n →
    IsSylowIn 2 T H → K ⊔ T = H → InFSq n H

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
