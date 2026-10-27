module

public import CFSG.Quasithin.Background.SmithB42Families

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

@[expose] def S16kG2IsU33 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 → ∀ (X : Type) [Group X],
    X ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆ → B42TypeU33 X

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
