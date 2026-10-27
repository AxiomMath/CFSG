module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint

@[expose] def FactG2DerivedOrder : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ =
      (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1))

end CFSG.Quasithin.Vol2.Ch11.SecA
