module

public import CFSG.Quasithin.EmptyFaithful.S14612DC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

@[expose] def NoE9Z4Large : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → IsE9Z4Shape T H p →
      2 ^ 9 < Nat.card ↥(pCoreOf 2 H) → False

end CFSG.Quasithin
