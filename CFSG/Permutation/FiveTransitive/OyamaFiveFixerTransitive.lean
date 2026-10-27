module

public import CFSG.Permutation.FiveTransitive.InvolutionPairFixerTransitivity
public import CFSG.Permutation.FiveTransitive.OyamaFivePairTransports

public section

namespace CFSG

namespace FiveTransitive.OyamaFiveFixerTransitive

open MulAction

theorem fixer_transitive
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (hsize : 10 ≤ Nat.card X)
    (hseed : CommutingFourSeed.Seed G X)
    (hmax : ∀ g : G, g * g = 1 → g ≠ 1 → (fixedBy X g).ncard ≤ 5)
    (a : G) (ha : a * a = 1) (hfixa : (fixedBy X a).ncard = 5) :
    ∀ x y : X, x ∉ fixedBy X a → y ∉ fixedBy X a →
      ∃ g : G, (∀ z ∈ fixedBy X a, g • z = z) ∧ g • x = y := by
  apply InvolutionPairFixerTransitivity.transitive_of_cross_pairs a ha
  intro t ht01 ht10 ht23 ht32
  exact OyamaFivePairTransports.exists_cross_pair
    hsize hseed hmax a ha hfixa t ht01 ht10 ht23 ht32

end FiveTransitive.OyamaFiveFixerTransitive

end CFSG
