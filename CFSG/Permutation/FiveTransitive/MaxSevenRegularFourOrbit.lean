module

public import CFSG.Permutation.FiveTransitive.HallRegularOrbits

public section

namespace CFSG

namespace FiveTransitive.MaxSevenRegularFourOrbit

open MulAction Research.HallOrbitTransitivity Research.HallRegularOrbits

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

omit [Finite G] in
private theorem exists_regular_point
    (hcard : 22 ≤ Fintype.card X)
    (hmax : ∀ t : G, orderOf t = 2 → (fixedBy X t).ncard ≤ 7)
    (a b : G) (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : Commute a b) (hne : a ≠ b) :
    ∃ z : X, z ∉ exceptionalSet (X := X) a b := by
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  have hab2 : (a * b) ^ 2 = 1 := by rw [hab.mul_pow, ha2, hb2, one_mul]
  have habne : a * b ≠ 1 := by
    intro he
    apply hne
    calc
      a = a * (b * b) := by rw [← pow_two, hb2, mul_one]
      _ = (a * b) * b := (mul_assoc _ _ _).symm
      _ = b := by rw [he, one_mul]
  have ho : orderOf (a * b) = 2 := orderOf_eq_prime_iff.mpr ⟨hab2, habne⟩
  have hecard : (exceptionalSet (X := X) a b).ncard ≤ 21 := by
    have h₁ := Set.ncard_union_le (fixedBy X a) (fixedBy X b)
    have h₂ := Set.ncard_union_le (fixedBy X a ∪ fixedBy X b) (fixedBy X (a * b))
    have hA := hmax a ha
    have hB := hmax b hb
    have hAB := hmax (a * b) ho
    change (fixedBy X a ∪ fixedBy X b ∪ fixedBy X (a * b)).ncard ≤ 21
    omega
  have hlt : (exceptionalSet (X := X) a b).ncard < (Set.univ : Set X).ncard := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card]
    omega
  obtain ⟨z, _, hz⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
  exact ⟨z, hz⟩

theorem exists_regular_four_set
    (hcard : 22 ≤ Fintype.card X)
    (hmax : ∀ t : G, orderOf t = 2 → (fixedBy X t).ncard ≤ 7)
    (a b : G) (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : Commute a b) (hne : a ≠ b) :
    ∃ z : X,
      (regularFourSet a b z).ncard = 4 ∧
      regularFourSet a b z ⊆ (exceptionalSet (X := X) a b)ᶜ ∧
      (∀ y ∈ regularFourSet a b z, a • y ∈ regularFourSet a b z) ∧
      (∀ y ∈ regularFourSet a b z, b • y ∈ regularFourSet a b z) := by
  obtain ⟨z, hz⟩ := exists_regular_point hcard hmax a b ha hb hab hne
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  exact ⟨z, regularFourSet_ncard_of_not_mem_exceptionalSet a b ha2 hb2 hab z hz,
    regularFourSet_subset_compl_exceptionalSet a b ha2 hb2 hab z hz,
    first_smul_mem_regularFourSet a b ha2 hab z,
    second_smul_mem_regularFourSet a b hb2 hab z⟩

end FiveTransitive.MaxSevenRegularFourOrbit

end CFSG
