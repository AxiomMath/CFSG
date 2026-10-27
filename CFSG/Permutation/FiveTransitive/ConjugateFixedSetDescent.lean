module

public import CFSG.Permutation.FiveTransitive.ConjugateMinimalOrbit
public import CFSG.Permutation.FiveTransitive.MinimalOrbitFixedSet

public section

namespace CFSG

namespace FiveTransitive.ConjugateFixedSetDescent

open MulAction ConjugateMinimalOrbit

theorem fixed_set_and_movement
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (P : Subgroup G) (a : G) (t : X)
    (hmin : ∀ y : X, y ∉ fixedPoints P X → Nat.card (orbit P t) ≤ Nat.card (orbit P y))
    (Q : Subgroup (conjugateSubgroup P a))
    (hQcard : Nat.card Q=Nat.card (stabilizer P t))
    (R : Subgroup (conjugateSubgroup P a)) (hQR : Q<R) :
    fixedPoints R X=fixedPoints (conjugateSubgroup P a) X ∧
      ∀ (g : conjugateSubgroup P a), g∉Q →
        ∀x∈fixedPoints Q X,x∉fixedPoints (conjugateSubgroup P a) X → g • x≠x := by
  have hmin' := minimal_orbit_conjugate P a t hmin
  have hcard := hQcard.trans (card_stabilizer_conjugate P a t)
  exact ⟨MinimalOrbitFixedSet.fixedPoints_eq_of_lt
    (conjugateSubgroup P a) X (a • t) hmin' Q hcard R hQR,
    fun g hg x hxQ hx => MinimalOrbitFixedSet.moves_fixed_complement
      (conjugateSubgroup P a) X (a • t) hmin' Q hcard g hg x hxQ hx⟩

end FiveTransitive.ConjugateFixedSetDescent

end CFSG
