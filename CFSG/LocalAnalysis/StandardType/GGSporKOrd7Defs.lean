module

public import CFSG.LocalAnalysis.StandardType.MarkingDict

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open

@[expose] def Ord7Param (t : StatedLieTag) (n p f : ℕ) : Prop :=
  ∀ (R : Type) [Group R] [Finite R], IsSimpleGroup R → LieModel R t n p f →
    (Nat.card (MulAut R)).factorization 7 ≤ (Nat.card R).factorization 7

@[expose] def Ord7Row (lab : LargeEvenLabel) : Prop :=
  Ord7Param (markTag lab) (markRank lab) (markChar lab) (markDeg lab)

end CFSG.StandardType.SporadicShape
