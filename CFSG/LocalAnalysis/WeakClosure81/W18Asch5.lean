module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def Asch2_10 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (H T K L : Subgroup Q),
    CFSG.Open.IsKGroup ↥H → IsSylowIn 2 T H → CFSG.Open.pRank 3 H ≤ 3 →
    IsComponentModN K H L → 3 ∣ K.relIndex L → L ⊔ T = H →
    Set.ncard {X : Subgroup Q | ∃ t ∈ T, X = conjSubgroup L t} ≤ 2

end CFSG.LocalAnalysis.WeakClosure81

end
