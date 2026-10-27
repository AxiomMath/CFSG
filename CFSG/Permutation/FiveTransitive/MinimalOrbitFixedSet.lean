module

public import CFSG.Permutation.FiveTransitive.MinimalOrbitStabilizer

public section

namespace CFSG

namespace FiveTransitive.MinimalOrbitFixedSet

open MulAction MinimalOrbitStabilizer

theorem moves_fixed_complement
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (t : X) (hmin : ∀ y : X, y ∉ fixedPoints G X → Nat.card (orbit G t) ≤ Nat.card (orbit G y))
    (Q : Subgroup G) (hQcard : Nat.card Q = Nat.card (stabilizer G t))
    (g : G) (hg : g ∉ Q) (x : X) (hxQ : x ∈ fixedPoints Q X)
    (hx : x ∉ fixedPoints G X) : g • x ≠ x := by
  intro he
  have hs := stabilizer_eq_of_minimal_orbit G X t hmin Q hQcard x hxQ hx
  have hmem : g ∈ stabilizer G x := he
  exact hg (hs ▸ hmem)

theorem fixedPoints_eq_of_lt
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (t : X) (hmin : ∀ y : X, y ∉ fixedPoints G X → Nat.card (orbit G t) ≤ Nat.card (orbit G y))
    (Q : Subgroup G) (hQcard : Nat.card Q = Nat.card (stabilizer G t))
    (R : Subgroup G) (hQR : Q < R) : fixedPoints R X = fixedPoints G X := by
  have hex : ∃ r : G, r ∈ R ∧ r ∉ Q := by
    by_contra! h
    exact hQR.not_ge h
  obtain ⟨r,hrR,hrQ⟩ := hex
  ext x
  constructor
  · intro hxR
    by_contra hx
    have hxQ : x ∈ fixedPoints Q X := by
      rw [mem_fixedPoints]
      intro q
      exact mem_fixedPoints.mp hxR ⟨q,hQR.le q.property⟩
    exact moves_fixed_complement G X t hmin Q hQcard r hrQ x hxQ hx
      (mem_fixedPoints.mp hxR ⟨r,hrR⟩)
  · intro hx
    rw [mem_fixedPoints]
    intro r
    exact mem_fixedPoints.mp hx (r:G)

end FiveTransitive.MinimalOrbitFixedSet

end CFSG
