module

public import CFSG.Permutation.FiveTransitive.TwoGroupQuadCommutatorOrbit
public import CFSG.Permutation.FiveTransitive.Degree67DerivedPairBound

public section

namespace CFSG

namespace FiveTransitive.Degree67QuadDerivedBound
open MulAction

theorem commutator_card_le_eight
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hG : IsPGroup 2 G) (hX : Fintype.card X = 67)
    (hF : Nat.card (fixedPoints G X) = 5)
    (horbit : ∀ x : X, Nat.card (orbit G x) ≤ 4)
    (hbound : ∀ g : G, g ≠ 1 → Nat.card (fixedBy X g) ≤ 33)
    (x : X) (hx : Nat.card (orbit G x) = 2) : Nat.card (commutator G) ≤ 8 := by
  classical
  let F := fixedPoints G X
  let O := orbit G x
  have hdis : Disjoint F O := by
    apply Set.disjoint_left.mpr
    intro y hyF hyO
    have he : orbit G y = orbit G x := orbit_eq_iff.mpr hyO
    have h1 := (mem_fixedPoints_iff_card_orbit_eq_one.mp hyF)
    rw [← Nat.card_eq_fintype_card,he,hx] at h1
    omega
  let s := (F ∪ O).toFinite.toFinset
  have hs : s.card = 7 := by
    change (F ∪ O).toFinite.toFinset.card = 7
    rw [← Set.ncard_eq_toFinset_card,Set.ncard_union_eq hdis,
      ← Nat.card_coe_set_eq,← Nat.card_coe_set_eq]
    change Nat.card (fixedPoints G X) + Nat.card (orbit G x) = 7
    omega
  apply Degree67DerivedPairBound.card_le_eight hX s hs
  · intro g y hy
    have hmem : y ∈ F ∪ O := (Set.Finite.mem_toFinset _).mp hy
    rcases hmem with hf | ho
    · exact hf g.val
    · exact TwoGroupQuadCommutatorOrbit.commutator_fixes_small_orbit x hx.le
        g.val g.property y ho
  · exact TwoGroupQuadCommutatorOrbit.all_commutator_orbits_le_two hG horbit
  · intro g hg
    exact hbound g.val (fun he => hg (Subtype.ext he))

end FiveTransitive.Degree67QuadDerivedBound

end CFSG
