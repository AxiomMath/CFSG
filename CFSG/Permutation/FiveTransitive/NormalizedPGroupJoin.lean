module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.NormalizedPGroupJoin

open MulAction

theorem isPGroup_join
    {G:Type*} [Group G] [Finite G] (Q:Subgroup G) (hQ:IsPGroup 2 Q)
    (a:G) (ha2:a^2=1) (hn:a∈Subgroup.normalizer (Q:Set G)) :
    IsPGroup 2 ↥(Subgroup.zpowers a ⊔ Q) := by
  have ha:IsPGroup 2 (Subgroup.zpowers a) := by
    have hd:orderOf a∣2 := orderOf_dvd_of_pow_eq_one ha2
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h|h
    · exact IsPGroup.of_card ((Nat.card_zpowers a).trans (h.trans (pow_zero 2).symm))
    · exact IsPGroup.of_card ((Nat.card_zpowers a).trans (h.trans (pow_one 2).symm))
  exact ha.to_sup_of_normal_right' hQ (Subgroup.zpowers_le.mpr hn)

theorem fixedPoints_join
    {G X:Type*} [Group G] [MulAction G X] (Q:Subgroup G) (a:G) :
    fixedPoints ↥(Subgroup.zpowers a ⊔ Q) X=fixedBy X a ∩ fixedPoints Q X := by
  ext x
  constructor
  · intro hx
    refine ⟨mem_fixedPoints.mp hx ⟨a,(le_sup_left:Subgroup.zpowers a≤Subgroup.zpowers a⊔Q) (Subgroup.mem_zpowers a)⟩,?_⟩
    rw [mem_fixedPoints]
    intro q
    exact mem_fixedPoints.mp hx ⟨q.val,(le_sup_right:Q≤Subgroup.zpowers a⊔Q) q.property⟩
  · rintro ⟨ha,hQ⟩
    have hle:Subgroup.zpowers a ⊔ Q≤stabilizer G x := by
      apply sup_le
      · exact Subgroup.zpowers_le.mpr ha
      · intro q hq
        exact mem_fixedPoints.mp hQ ⟨q,hq⟩
    exact mem_fixedPoints.mpr fun q => hle q.property

end FiveTransitive.NormalizedPGroupJoin

end CFSG
