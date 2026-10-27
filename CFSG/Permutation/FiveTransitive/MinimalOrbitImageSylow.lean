module

public import CFSG.Permutation.FiveTransitive.MinimalOrbitFixerSylow
public import CFSG.Permutation.FiveTransitive.SylowImagePointStabilizer

public section

namespace CFSG

namespace FiveTransitive.MinimalOrbitImageSylow

open MulAction GenericSylowFixedAction

theorem exists_sylow_with_chosen_image
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    (s : Set X) {p : ℕ} [Fact p.Prime] (S : Sylow p (fixingSubgroup G s))
    (hfixed : fixedPoints (sylowImage G X s S) X = s)
    (x : X) (hx : x ∉ s)
    (hmin : ∀ y : X, y ∉ fixedPoints (sylowImage G X s S) X →
      Nat.card (orbit (sylowImage G X s S) x) ≤ Nat.card (orbit (sylowImage G X s S) y)) :
    ∃ T : Sylow p (fixingSubgroup G (insert x s)),
      sylowImage G X (insert x s) T =
        (stabilizer (sylowImage G X s S) x).map (sylowImage G X s S).subtype := by
  have hfixed' : fixedPoints S X = s := by
    rwa [SylowImagePointStabilizer.fixed_eq] at hfixed
  have hmin' : ∀ y : X, y ∉ fixedPoints S X → Nat.card (orbit S x) ≤ Nat.card (orbit S y) := by
    intro y hy
    have h := hmin y (by rwa [SylowImagePointStabilizer.fixed_eq])
    simpa only [SylowImagePointStabilizer.orbit_eq] using h
  obtain ⟨T,hT⟩ := MinimalOrbitFixerSylow.sylow_of_minimal_orbit G X s S hfixed' x hx hmin'
  refine ⟨T, ?_⟩
  rw [SylowImagePointStabilizer.stabilizer_image_eq]
  exact hT

end FiveTransitive.MinimalOrbitImageSylow

end CFSG
