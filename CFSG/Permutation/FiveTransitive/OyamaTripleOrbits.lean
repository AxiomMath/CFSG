module

public import CFSG.Permutation.FiveTransitive.OyamaTripleSylow
public import CFSG.Permutation.FiveTransitive.SylowThreeFixedOrbits

public section

namespace CFSG

namespace FiveTransitive.OyamaTripleOrbits

open MulAction OyamaTripleSylow

variable {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]

private theorem complement_fixed_card
    (heven : Even (Nat.card X)) (hfour : FourFixedSix G X)
    (s : Set X) (hs : s.ncard = 3) (S : Sylow 2 (fixingSubgroup G s)) :
    Nat.card (fixedPoints S (SubMulAction.ofFixingSubgroup G s)) = 3 := by
  classical
  let Y := SubMulAction.ofFixingSubgroup G s
  have heq := OyamaMinimalOrbitChoice.fixedPoints_map_subtype
    (fixingSubgroup G s) (S : Subgroup (fixingSubgroup G s)) (X := X)
  have h6 : (fixedPoints S X).ncard = 6 := by
    rw [← heq]
    exact triple_sylow_fixed_six heven hfour s hs S
  have hbase : s ⊆ fixedPoints S X := by
    rw [← heq]
    exact base_subset_fixed s S
  let e : fixedPoints S Y ≃ ↥(fixedPoints S X \ s) :=
    { toFun := fun y => ⟨y.val.val, ⟨by
        rw [mem_fixedPoints]
        intro q
        exact congrArg Subtype.val (mem_fixedPoints.mp y.property q), y.val.property⟩⟩
      invFun := fun y => ⟨⟨y.val, y.property.2⟩, by
        rw [mem_fixedPoints]
        intro q
        apply Subtype.ext
        exact mem_fixedPoints.mp y.property.1 q⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_sdiff hbase, h6, hs]

theorem card_orbits_eq_one_or_three
    (heven : Even (Nat.card X)) (hfour : FourFixedSix G X)
    (s : Set X) (hs : s.ncard = 3) :
    Nat.card (orbitRel.Quotient (fixingSubgroup G s)
      (SubMulAction.ofFixingSubgroup G s)) = 1 ∨
    Nat.card (orbitRel.Quotient (fixingSubgroup G s)
      (SubMulAction.ofFixingSubgroup G s)) = 3 := by
  classical
  let S : Sylow 2 (fixingSubgroup G s) := Classical.choice inferInstance
  apply SylowThreeFixedOrbits.card_orbits_eq_one_or_three S
    (complement_fixed_card heven hfour s hs S)
  intro y
  obtain ⟨T,hT⟩ := exists_triple_sylow_fixing heven hfour s hs y.val y.property
  refine ⟨T, ?_⟩
  rw [mem_fixedPoints]
  intro q
  apply Subtype.ext
  exact mem_fixedPoints.mp hT q

end FiveTransitive.OyamaTripleOrbits

end CFSG
