module

public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

@[expose] def FactG2Simple : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    IsSimpleGroup ↥⁅quasithinG2 K, quasithinG2 K⁆

end CFSG.Quasithin.Vol2.Ch11.SecB
