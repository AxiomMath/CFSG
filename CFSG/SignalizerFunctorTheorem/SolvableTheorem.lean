module

public import CFSG.SignalizerFunctorTheorem.Main
public import CFSG.SignalizerFunctorTheorem.Glauberman.Final

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem

theorem solvableRankOneTheorem : SolvableRankOneTheorem :=
  solvableRankOneTheorem_of_twoThreeCase fun p hp _ => Glauberman.twoThreeCase p hp

theorem glauberman_solvable_signalizer_functor
    (G : Type) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime)
    (A : Subgroup G) (hA : IsMulCommutative A) (hexp : ∀ a ∈ A, a ^ p = 1)
    (hrank : p ^ 3 ∣ Nat.card A)
    (θ : G → Subgroup G) (hθ : IsSolvableSignalizerFunctor p A θ) :
    let W : Subgroup G := ⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1), θ a
    Nat.Coprime p (Nat.card W) ∧ Group.IsSolvable W ∧
      ∀ a ∈ A, a ≠ 1 → θ a = W ⊓ Subgroup.centralizer {a} :=
  glauberman_of_solvableRankOne solvableRankOneTheorem G p hp A hA hexp hrank θ hθ

end CFSG.SignalizerFunctorTheorem
