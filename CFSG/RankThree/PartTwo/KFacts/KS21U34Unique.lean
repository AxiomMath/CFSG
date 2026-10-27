module

public import CFSG.RankThree.PartTwo.KFacts.KS21U34
public import CFSG.RankThree.PartTwo.Sec21.Item22KDef

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS21.U34

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem card_eq_three_of_isPGroup {X : Type} [Group X] (hX : StatedClassicalModel X .PSU 3 2 2)
    {S : Subgroup X} (hS : IsPGroup 3 S) (hS1 : S ≠ ⊥) : Nat.card S = 3 := by
  obtain ⟨φ⟩ := nonempty_equiv_Y hX
  have hcard : Nat.card X = 62400 := by rw [Nat.card_congr φ.toEquiv, card_Y]
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hdvd : 3 ^ k ∣ 62400 := by
    rw [← hk, ← hcard]
    exact Subgroup.card_subgroup_dvd_card S
  have hk1 : k ≤ 1 := by
    by_contra h
    have : 3 ^ 2 ∣ 62400 := (pow_dvd_pow 3 (by omega)).trans hdvd
    norm_num at this
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hk
    exact hS1 hk
  rw [hk, show k = 1 by omega, pow_one]

theorem u34UniqueL24 : Sec21.U34UniqueL24 := fun _ _ _ hX S hS hS1 =>
  existsUnique_psl24_of_card_three hX S (card_eq_three_of_isPGroup hX hS hS1)

end CFSG.RankThree.PartTwo.KFacts.KS21.U34
