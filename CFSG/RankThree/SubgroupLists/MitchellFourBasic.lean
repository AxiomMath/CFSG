module

public import CFSG.RankThree.SubgroupLists.MitchellDicksonTwo

public section

namespace CFSG.RankThree.SubgroupLists

open CFSG.BenderSuzuki.MatrixGroups

theorem perm_four_sq_comm : ∀ a b : Equiv.Perm (Fin 4), a ^ 4 = 1 → a ^ 2 ≠ 1 → b ^ 4 = 1 →
    b ^ 2 ≠ 1 → a ^ 2 * b ^ 2 = b ^ 2 * a ^ 2 := by
  decide +kernel

theorem perm_four_commutator_pow_three : ∀ a b : Equiv.Perm (Fin 4), a ^ 4 = 1 → a ^ 2 ≠ 1 →
    b ^ 4 = 1 → b ^ 2 ≠ 1 → a * b ≠ b * a →
      (a * b * a⁻¹ * b⁻¹) ^ 3 = 1 ∧ a * b * a⁻¹ * b⁻¹ ≠ 1 := by
  decide +kernel

private theorem pow_four_eq_one_and_sq_ne_one_of_orderOf {M : Type*} [Monoid M] {a : M}
    (ha : orderOf a = 4) : a ^ 4 = 1 ∧ a ^ 2 ≠ 1 := by
  refine ⟨ha ▸ pow_orderOf_eq_one a, fun h => ?_⟩
  have := Nat.le_of_dvd two_pos (ha ▸ orderOf_dvd_of_pow_eq_one h)
  omega

section Dickson

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]

theorem sq_mul_sq_comm_of_orderOf_four (hF : Nat.card F = p ^ f)
    (X : Subgroup (PSL2MatrixGroup F)) (hX : ¬ p ∣ Nat.card X) {x y : X} (hx : orderOf x = 4)
    (hy : orderOf y = 4) : x ^ 2 * y ^ 2 = y ^ 2 * x ^ 2 := by
  by_cases hxy : x * y = y * x
  · exact ((show Commute x y from hxy).pow_pow 2 2).eq
  obtain ⟨e⟩ := nonempty_mulEquiv_perm_four hF X hX hx hy hxy
  obtain ⟨hx4, hx2⟩ := pow_four_eq_one_and_sq_ne_one_of_orderOf (e.orderOf_eq x ▸ hx)
  obtain ⟨hy4, hy2⟩ := pow_four_eq_one_and_sq_ne_one_of_orderOf (e.orderOf_eq y ▸ hy)
  apply e.injective
  simpa only [map_mul, map_pow] using perm_four_sq_comm (e x) (e y) hx4 hx2 hy4 hy2

theorem commutator_pow_three_of_orderOf_four
    (hF : Nat.card F = p ^ f) (X : Subgroup (PSL2MatrixGroup F)) (hX : ¬ p ∣ Nat.card X)
    {x y : X} (hx : orderOf x = 4) (hy : orderOf y = 4) (hxy : x * y ≠ y * x) :
    (x * y * x⁻¹ * y⁻¹) ^ 3 = 1 ∧ x * y * x⁻¹ * y⁻¹ ≠ 1 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_perm_four hF X hX hx hy hxy
  obtain ⟨hx4, hx2⟩ := pow_four_eq_one_and_sq_ne_one_of_orderOf (e.orderOf_eq x ▸ hx)
  obtain ⟨hy4, hy2⟩ := pow_four_eq_one_and_sq_ne_one_of_orderOf (e.orderOf_eq y ▸ hy)
  have hexy : e x * e y ≠ e y * e x := by
    rw [← map_mul, ← map_mul]
    exact e.injective.ne hxy
  obtain ⟨h3, h1⟩ := perm_four_commutator_pow_three (e x) (e y) hx4 hx2 hy4 hy2 hexy
  refine ⟨e.injective ?_, fun h => h1 ?_⟩
  · simpa only [map_mul, map_pow, map_inv, map_one] using h3
  · simpa only [map_mul, map_inv, map_one] using congrArg e h

end Dickson

end CFSG.RankThree.SubgroupLists
