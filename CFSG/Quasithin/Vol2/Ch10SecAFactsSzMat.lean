module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.LieType.Ree.SmallReeFrattiniTorusNormalizer

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Blueprint CFSG.LieType.Ree

variable {a : ℕ} {K : Type} [Field K]

theorem fixed_suzukiS {Y : Fin 4 → K} (h : ∀ u v : K, (suzukiS a u v).mulVec Y = Y) :
    Y 0 = 0 ∧ Y 1 = 0 ∧ Y 2 = 0 := by
  have h1 := congrFun (h 1 0) 1
  have h2 := congrFun (h 1 0) 2
  have h3 := congrFun (h 1 0) 3
  simp [suzukiS, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at h1 h2 h3
  have e0 : Y 0 = 0 := by linear_combination h1
  have e1 : Y 1 = 0 := by linear_combination h2
  refine ⟨e0, e1, ?_⟩
  rw [e0, e1] at h3
  linear_combination h3

theorem suzukiS_mulVec_e4 (u v z : K) :
    (suzukiS a u v).mulVec ![0, 0, 0, z] = ![0, 0, 0, z] := by
  ext i
  fin_cases i <;> simp [suzukiS, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem suzukiD_mulVec_e4 (l : Kˣ) (z : K) :
    (suzukiD a l).mulVec ![0, 0, 0, z] =
      ![0, 0, 0, ((l ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K) * z] := by
  ext i
  fin_cases i <;> simp [suzukiD, Matrix.mulVec_diagonal]

theorem coprime_two_pow_add_one (a : ℕ) : Nat.Coprime (2 ^ a + 1) (2 ^ (2 * a + 1) - 1) := by
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have h : 2 ^ (2 * a + 1) - 1 = (2 * 2 ^ a - 2) * (2 ^ a + 1) + 1 := by
    have e : 2 ^ (2 * a + 1) = 2 * 2 ^ a * 2 ^ a := by ring
    rw [e]
    zify [Nat.one_le_two_pow, (by omega : 2 ≤ 2 * 2 ^ a),
      (by nlinarith : 1 ≤ 2 * 2 ^ a * 2 ^ a)]
    ring
  rw [h, Nat.coprime_mul_right_add_right]
  exact Nat.coprime_one_right _

theorem eq_one_of_zpow_eq_one [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {l : Kˣ}
    (h : l ^ (-1 - (2 ^ a : ℤ)) = 1) : l = 1 := by
  have h1 : l ^ (2 ^ a + 1) = 1 := by
    have h2 : l ^ (-1 - (2 ^ a : ℤ)) = (l ^ (2 ^ a + 1))⁻¹ := by
      rw [← zpow_natCast, ← zpow_neg]
      congr 1
      push_cast
      ring
    rw [h2, inv_eq_one] at h
    exact h
  have h3 : l ^ (2 ^ (2 * a + 1) - 1) = 1 := by
    rw [← hK, ← Nat.card_units]
    exact pow_card_eq_one'
  have h4 := pow_gcd_eq_one.mpr ⟨h1, h3⟩
  rwa [(coprime_two_pow_add_one a).gcd_eq_one, pow_one] at h4

end CFSG.Quasithin.Vol2.Ch10.SecA
