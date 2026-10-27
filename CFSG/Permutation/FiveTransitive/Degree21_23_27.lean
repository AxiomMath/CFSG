module

public import CFSG.Permutation.FiveTransitive.FourFixedPrimeCycle

public section

namespace CFSG

namespace FiveTransitive.Degree21_23_27

open MulAction SubMulAction Subgroup

private theorem prime_dvd_card_of_five_transitive
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    {n p index : ℕ}
    (hcard : Fintype.card X = n)
    (hnFive : 5 ≤ n)
    (hindex : n.descFactorial 5 = index)
    (hpindex : p ∣ index)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i) :
    p ∣ Nat.card P := by
  classical
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  obtain ⟨s, _, hs⟩ :=
    Set.exists_subset_card_eq
      (s := (Set.univ : Set X)) (n := 5) (by
        rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
        exact hnFive)
  have hfixIndex := hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hfixIndex
  have hdesc :
      n.descFactorial 5 * (n - 5).factorial = n.factorial := by
    rw [Nat.mul_comm, Nat.factorial_mul_descFactorial hnFive]
  have hactual :
      (fixingSubgroup P s).index = index := by
    rw [← hindex]
    nlinarith [Nat.factorial_pos (n - 5)]
  have hindexCard := (fixingSubgroup P s).index_mul_card
  rw [hactual] at hindexCard
  rw [← hindexCard]
  exact dvd_mul_of_dvd_left hpindex _

private theorem alternatingGroup_le_of_five_transitive_of_card_eq_twentyOne
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 21)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i) :
    alternatingGroup X ≤ P := by
  apply FourFixedPrimeCycle.alternatingGroup_le_of_prime_dvd_card
      X P (p := 17) (by norm_num) (by norm_num) (by norm_num)
      (by omega) h5
  apply prime_dvd_card_of_five_transitive
      X P (n := 21) (index := 2441880) hcard (by norm_num)
  · norm_num [Nat.descFactorial]
  · norm_num
  · exact h5

private theorem alternatingGroup_le_of_five_transitive_of_card_eq_twentyThree
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 23)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i) :
    alternatingGroup X ≤ P := by
  apply FourFixedPrimeCycle.alternatingGroup_le_of_prime_dvd_card
      X P (p := 19) (by norm_num) (by norm_num) (by norm_num)
      (by omega) h5
  apply prime_dvd_card_of_five_transitive
      X P (n := 23) (index := 4037880) hcard (by norm_num)
  · norm_num [Nat.descFactorial]
  · norm_num
  · exact h5

private theorem alternatingGroup_le_of_five_transitive_of_card_eq_twentySeven
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 27)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i) :
    alternatingGroup X ≤ P := by
  apply FourFixedPrimeCycle.alternatingGroup_le_of_prime_dvd_card
      X P (p := 23) (by norm_num) (by norm_num) (by norm_num)
      (by omega) h5
  apply prime_dvd_card_of_five_transitive
      X P (n := 27) (index := 9687600) hcard (by norm_num)
  · norm_num [Nat.descFactorial]
  · norm_num
  · exact h5

private theorem classification_of_five_transitive_of_alternating_forced
    (G X : Type) [Group G] [Fintype G] [Fintype X] [DecidableEq X]
    [MulAction G X] [FaithfulSMul G X]
    {n : ℕ} (hcard : Fintype.card X = n)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i)
    (hforce :
      ∀ (P : Subgroup (Equiv.Perm X)),
        (∀ a b : Fin 5 → X,
          Function.Injective a → Function.Injective b →
          ∃ g : P, ∀ i, g • a i = b i) →
        alternatingGroup X ≤ P)
    (hnSeven : 7 ≤ n) :
    Fintype.card G = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧
        Fintype.card G = (Fintype.card X).factorial / 2) := by
  classical
  let φ : G →* Equiv.Perm X :=
    MulAction.toPermHom G X
  let P : Subgroup (Equiv.Perm X) := φ.range
  have h5P :
      ∀ a b : Fin 5 → X,
        Function.Injective a → Function.Injective b →
        ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g, hg⟩ := h5 a b ha hb
    refine ⟨⟨φ g, ⟨g, rfl⟩⟩, ?_⟩
    intro i
    exact hg i
  exact FiveTransitive.Helpers.card_classification_of_alternatingGroup_le
    G X (by omega) (hforce P h5P)

theorem classification_of_five_transitive_of_card_eq_twentyOne
    (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : Fintype.card X = 21)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    Fintype.card G = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧
        Fintype.card G = (Fintype.card X).factorial / 2) := by
  classical
  apply classification_of_five_transitive_of_alternating_forced
      G X hcard h5
  · intro P h5P
    exact alternatingGroup_le_of_five_transitive_of_card_eq_twentyOne
      X P hcard h5P
  · norm_num

theorem classification_of_five_transitive_of_card_eq_twentyThree
    (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : Fintype.card X = 23)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    Fintype.card G = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧
        Fintype.card G = (Fintype.card X).factorial / 2) := by
  classical
  apply classification_of_five_transitive_of_alternating_forced
      G X hcard h5
  · intro P h5P
    exact alternatingGroup_le_of_five_transitive_of_card_eq_twentyThree
      X P hcard h5P
  · norm_num

theorem classification_of_five_transitive_of_card_eq_twentySeven
    (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : Fintype.card X = 27)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    Fintype.card G = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧
        Fintype.card G = (Fintype.card X).factorial / 2) := by
  classical
  apply classification_of_five_transitive_of_alternating_forced
      G X hcard h5
  · intro P h5P
    exact alternatingGroup_le_of_five_transitive_of_card_eq_twentySeven
      X P hcard h5P
  · norm_num

end FiveTransitive.Degree21_23_27

end CFSG
