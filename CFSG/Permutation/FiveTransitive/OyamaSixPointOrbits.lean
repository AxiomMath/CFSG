module

public import CFSG.Permutation.FiveTransitive.OyamaPointOrbitGeometry
public import CFSG.Permutation.FiveTransitive.OyamaSixOddOrbits

public section

namespace CFSG

namespace FiveTransitive.OyamaSixPointOrbits

open MulAction

theorem exists_geometry
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s))
    (hH : fixedPoints (fixingSubgroup G s) X = s)
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hcard : (fixedPoints S X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (OyamaSixElementary.fixedHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (hS : Nat.card S = 16) :
    ∃ u v w : X, u ∉ s ∧ v ∉ s ∧ u ≠ v ∧ fixedPoints S X = s ∪ {u,v} ∧
      v ∉ orbit (fixingSubgroup G s) u ∧
      (¬ 2 ∣ Nat.card (orbit (fixingSubgroup G s) u)) ∧
      (¬ 2 ∣ Nat.card (orbit (fixingSubgroup G s) v)) ∧
      Nat.card (orbit (fixingSubgroup G s) u) = Nat.card (orbit (fixingSubgroup G s) v) ∧
      1 < Nat.card (orbit (fixingSubgroup G s) u) ∧
      1 < Nat.card (orbit (fixingSubgroup G s) v) ∧
      w ∉ s ∪ orbit (fixingSubgroup G s) u ∪ orbit (fixingSubgroup G s) v := by
  have hd := (OyamaSixOddOrbits.degree_and_odd_orbits G X h4 s hs S hfree hcard himage hS).2.1
  exact OyamaPointOrbitGeometry.exists_geometry G X s hs S hH hcard himage hS hfree hd

end FiveTransitive.OyamaSixPointOrbits

end CFSG
