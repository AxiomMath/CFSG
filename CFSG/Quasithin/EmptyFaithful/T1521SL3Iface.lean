module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.L3Aut

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def L3ModelAut : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (H : Type) [Group H], (H ≃* projectiveSL 3 K) →
      ∀ (Q : Sylow 2 H) (α : MulAut H),
        (∀ z ∈ Subgroup.normalizer ((Q : Subgroup H) : Set H), Odd (orderOf z) → α z = z) →
          α = 1

end CFSG.Quasithin.L3Aut
