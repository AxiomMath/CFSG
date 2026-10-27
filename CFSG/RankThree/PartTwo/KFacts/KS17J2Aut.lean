module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartTwo.KFacts

@[expose] def KS17J2AutThree : Prop :=
  ∀ (X : Type) [Group X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ σ : MulAut X, σ ^ 3 = 1 → σ ∈ (MulAut.conj : X →* MulAut X).range

end CFSG.RankThree.PartTwo.KFacts
