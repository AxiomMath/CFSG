module

public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

@[expose] def conjClosure {G : Type*} [Group G] (H : Subgroup G) (s : G) : Subgroup G :=
  Subgroup.closure {x | ∃ g ∈ H, x = g⁻¹ * s * g}

@[expose] def OrdData (m : ℕ) : Prop :=
  ∃ N e p : ℕ, (∃ r, Odd r ∧ m = 2 ^ N * r) ∧ 7 ≤ e ∧
    CFSG.Timmesfeld.IsPrimitivePrimeDivisor p e ∧ p ∣ m ∧ 2 * N ≤ 3 * e ∧
    (2 * N = 3 * e → 9 ≤ e) ∧ m < 2 ^ (3 * N)

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
