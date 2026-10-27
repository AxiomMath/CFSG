module

public import CFSG.Permutation.FiveTransitive.TupleSemiregularFixedDegree
public import CFSG.Permutation.FiveTransitive.HallEvenTupleStabilizer
public import CFSG.Permutation.FiveTransitive.OyamaSixFixedBranch

public section

namespace CFSG

namespace FiveTransitive.SemiregularFiveHallObstruction

open MulAction TupleSemiregularFour

theorem involution_fixed_le_five
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h5 : IsMultiplyPretransitive G X 5) (e : Fin 5 ↪ X)
    (S : Sylow 2 (stabilizer G e))
    (hfix : Nat.card (fixedPoints (image e S) X) = 5)
    (hfree : ∀ q : G, q ∈ image e S → q ≠ 1 →
      ∀ x : X, x ∉ fixedPoints (image e S) X → q • x ≠ x)
    (g : G) (hg : orderOf g = 2) : (fixedBy X g).ncard ≤ 5 := by
  by_cases hge : 5 ≤ (fixedBy X g).ncard
  · exact (TupleSemiregularFixedDegree.involution_fixed_card G X 5 h5 e S
      hfix hfree g hg hge).le
  · omega

theorem involution_fixed_five_of_four
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hodd : Odd (Nat.card X))
    (hbound : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 5)
    (g : G) (hg : orderOf g = 2) (hge : 4 ≤ (fixedBy X g).ncard) :
    (fixedBy X g).ncard = 5 := by
  have hcyc : IsPGroup 2 (Subgroup.zpowers g) := IsPGroup.of_card
    (n := 1) (by simp only [Nat.card_zpowers, hg, pow_one])
  have hmod := hcyc.card_modEq_card_fixedPoints X
  rw [OyamaSixFixedBranch.fixedPoints_zpowers_eq_fixedBy, Nat.card_coe_set_eq] at hmod
  have ho := Nat.odd_iff.mp hodd
  have hb := hbound g hg
  change Nat.card X % 2 = (fixedBy X g).ncard % 2 at hmod
  omega

theorem not_six_transitive
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hcard : 29 ≤ Nat.card X)
    (hbound : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 5) :
    ¬ IsMultiplyPretransitive G X 6 := by
  intro h6
  let e : Fin 6 ↪ X := (Fin.castLEEmb (show 6 ≤ Nat.card X by omega)).trans
    (Finite.equivFin X).symm.toEmbedding
  obtain ⟨g, hg, hge⟩ := HallEvenTupleStabilizer.exists_involution_fixing_six G X hcard h6 e
  have hsub : Set.range e ⊆ fixedBy X g := by
    rintro x ⟨i, rfl⟩
    exact hge i
  have hcount := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_range_of_injective e.injective, Nat.card_fin] at hcount
  have := hbound g hg
  omega

end FiveTransitive.SemiregularFiveHallObstruction

end CFSG
