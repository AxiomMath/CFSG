module

public import CFSG.SignalizerFunctorTheorem.Solvable.Completeness
public import CFSG.SignalizerFunctorTheorem.Solvable.ZJControl

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Solvable

theorem fiveCase (prime rank : ℕ) (prime_prime : prime.Prime) : FiveCase prime rank :=
  fun _ _ _ actor elementary large values conditions locally_complete q hq hq5 =>
    complete_of_locallyComplete_of_five_le prime rank q prime_prime hq.1 hq5 actor elementary
      large values conditions locally_complete hq

theorem complete_of_le_three (prime rank : ℕ) (prime_prime : prime.Prime) (hp3 : prime ≤ 3)
    (G : Type) [Group G] [Finite G] (actor : Subgroup G) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor) (values : Subgroup G → Subgroup G)
    (conditions : SolvableSignalizerConditions prime rank actor values) :
    solvableSignalizerCompatible prime rank actor values
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) :=
  complete_of_twoThreeCase prime rank prime_prime (fiveCase prime rank prime_prime)
    (twoThreeCase_of_le_three prime rank prime_prime hp3) G actor elementary large values
    conditions

theorem solvableRankOneTheoremAt_of_le_three (p : ℕ) (hp : p.Prime) (hp3 : p ≤ 3) :
    SolvableRankOneTheoremAt p :=
  solvableRankOneTheoremAt_of_cases p hp (fiveCase p 1 hp) (twoThreeCase_of_le_three p 1 hp hp3)

theorem glauberman_of_le_three
    (G : Type) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (hp3 : p ≤ 3)
    (A : Subgroup G) (hA : IsMulCommutative A) (hexp : ∀ a ∈ A, a ^ p = 1)
    (hrank : p ^ 3 ∣ Nat.card A)
    (θ : G → Subgroup G) (hθ : IsSolvableSignalizerFunctor p A θ) :
    let W : Subgroup G := ⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1), θ a
    Nat.Coprime p (Nat.card W) ∧ Group.IsSolvable W ∧
      ∀ a ∈ A, a ≠ 1 → θ a = W ⊓ Subgroup.centralizer {a} :=
  glauberman_of_solvableRankOneAt G p hp (solvableRankOneTheoremAt_of_le_three p hp hp3) A hA hexp
    hrank θ hθ

end CFSG.SignalizerFunctorTheorem.Solvable
