module

public import CFSG.LocalAnalysis.StandardType.GGSporKBMPreds

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

@[expose] def BSevenOrd (K : Type) [Group K] [Finite K] : Prop :=
  ∀ L : Subgroup K, IsSimpleGroup L → StandardType.LargeEvenMarking L (fun _ _ _ _ _ _ => True) →
    (Nat.card (MulAut ↥L)).factorization 7 ≤ (Nat.card ↥L).factorization 7

end CFSG.StandardType.SporadicShape
