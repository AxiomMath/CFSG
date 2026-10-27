module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup

@[expose] def KFactShape92NoFaithfulA5 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Shape92 S →
    ∀ Q K : Subgroup S, Q ≠ ⊥ → (∀ a ∈ Q, a ^ 2 = 1) → K ≤ normalizer (Q : Set S) →
      IsAlt (Bar2 K) 5 → ¬ K ⊓ centralizer (Q : Set S) ≤ pCoreOf 2 K

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
