module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

private theorem k91np_shift (k l K L : ℕ) (hk : k % 3 = K % 3) (hl : l % 3 = L % 3) :
    ∃ α β : ℕ, α < 2 ∧ β < 2 ∧ (k + 5 * (3 * α + 3 * β)) % 6 = K % 6 ∧
      (l + 5 * (3 * α + 2 * (3 * β))) % 6 = L % 6 := by
  rcases (by omega : ((k % 6 = K % 6 ∧ l % 6 = L % 6) ∨ ((k + 15) % 6 = K % 6 ∧ l % 6 = L % 6)) ∨
      ((k + 15) % 6 = K % 6 ∧ (l + 15) % 6 = L % 6) ∨ (k % 6 = K % 6 ∧ (l + 15) % 6 = L % 6)) with
    (h | h) | h | h
  · exact ⟨0, 0, by omega, by omega, by omega, by omega⟩
  · exact ⟨0, 1, by omega, by omega, by omega, by omega⟩
  · exact ⟨1, 0, by omega, by omega, by omega, by omega⟩
  · exact ⟨1, 1, by omega, by omega, by omega, by omega⟩

private theorem k91np_arith (k l : ℕ) :
    ∃ α β t k' l' : ℕ, α < 2 ∧ β < 2 ∧ (t = 1 ∨ t = 5) ∧ k' < 2 ∧ l' < 3 ∧
      (k + 5 * (3 * α + 3 * β)) % 6 = (t * k') % 6 ∧
      (l + 5 * (3 * α + 2 * (3 * β))) % 6 = (t * l') % 6 := by
  by_cases h : k % 3 = 2
  · obtain ⟨α, β, hα, hβ, h1, h2⟩ := k91np_shift k l (5 * 1) (5 * ((2 * l) % 3)) (by omega)
      (by omega)
    exact ⟨α, β, 5, 1, (2 * l) % 3, hα, hβ, Or.inr rfl, by omega, by omega, h1, h2⟩
  · obtain ⟨α, β, hα, hβ, h1, h2⟩ := k91np_shift k l (1 * (k % 3)) (1 * (l % 3)) (by omega)
      (by omega)
    exact ⟨α, β, 1, k % 3, l % 3, hα, hβ, Or.inl rfl, by omega, by omega, h1, h2⟩

private theorem k91np_pow_congr {H : Type*} [Group H] {z : H} (hz6 : z ^ 6 = 1) {e f : ℕ}
    (h : e % 6 = f % 6) : z ^ e = z ^ f :=
  (pow_eq_pow_mod e hz6).trans ((congrArg (z ^ ·) h).trans (pow_eq_pow_mod f hz6).symm)

private theorem k91np_expand {H : Type*} [Group H] {x y z : H} (hxz : Commute x z)
    (hyz : Commute y z) (a b : ℕ) :
    (x * z ^ a) ^ 2 = x ^ 2 * z ^ (2 * a) ∧ (y * z ^ b) ^ 4 = y ^ 4 * z ^ (4 * b) ∧
      (x * z ^ a * (y * z ^ b)) ^ 5 = (x * y) ^ 5 * z ^ (5 * (a + b)) ∧
      (x * z ^ a * (y * z ^ b) * (y * z ^ b)) ^ 5 = (x * y * y) ^ 5 * z ^ (5 * (a + 2 * b)) := by
  have hx' : ∀ m : ℕ, Commute x (z ^ m) := fun m => hxz.pow_right m
  have hy' : ∀ m : ℕ, Commute y (z ^ m) := fun m => hyz.pow_right m
  have hxy' : ∀ m : ℕ, Commute (x * y) (z ^ m) := fun m => (hx' m).mul_left (hy' m)
  have hxyy' : ∀ m : ℕ, Commute (x * y * y) (z ^ m) := fun m => (hxy' m).mul_left (hy' m)
  have e3 : x * z ^ a * (y * z ^ b) = x * y * z ^ (a + b) := by
    rw [(hy' a).symm.mul_mul_mul_comm x, ← pow_add]
  have e4 : x * z ^ a * (y * z ^ b) * (y * z ^ b) = x * y * y * z ^ (a + 2 * b) := by
    rw [e3, (hy' (a + b)).symm.mul_mul_mul_comm (x * y), ← pow_add,
      show a + b + b = a + 2 * b by omega]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [(hx' a).mul_pow, ← pow_mul, Nat.mul_comm a 2]
  · rw [(hy' b).mul_pow, ← pow_mul, Nat.mul_comm b 4]
  · rw [e3, (hxy' (a + b)).mul_pow, ← pow_mul, Nat.mul_comm (a + b) 5]
  · rw [e4, (hxyy' (a + 2 * b)).mul_pow, ← pow_mul, Nat.mul_comm (a + 2 * b) 5]

theorem exists_normalized_params {H : Type*} [Group H] {n : ℕ} (hn : n = 3 ∨ n = 6) {x y z : H}
    (hxz : Commute x z) (hyz : Commute y z) (hzn : z ^ n = 1) {i j k l : ℕ}
    (hx : x ^ 2 = z ^ (3 * i)) (hy : y ^ 4 = z ^ (3 * j)) (hxy : (x * y) ^ 5 = z ^ k)
    (hxyy : (x * y * y) ^ 5 = z ^ l) :
    ∃ (a b : ℕ) (z' : H) (k' l' : ℕ), (z' = z ∨ z' = z⁻¹) ∧ k' < 2 ∧ l' < 3 ∧
      (x * z ^ a) ^ 2 = z' ^ (3 * i) ∧ (y * z ^ b) ^ 4 = z' ^ (3 * j) ∧
      (x * z ^ a * (y * z ^ b)) ^ 5 = z' ^ k' ∧
      (x * z ^ a * (y * z ^ b) * (y * z ^ b)) ^ 5 = z' ^ l' := by
  have hz6 : z ^ 6 = 1 := by
    rcases hn with rfl | rfl
    · rw [show 6 = 3 * 2 from rfl, pow_mul, hzn, one_pow]
    · exact hzn
  obtain ⟨α, β, t, k', l', -, -, ht, hk', hl', h1, h2⟩ := k91np_arith k l
  obtain ⟨e1, e2, e3, e4⟩ := k91np_expand hxz hyz (3 * α) (3 * β)
  refine ⟨3 * α, 3 * β, z ^ t, k', l', ?_, hk', hl', ?_, ?_, ?_, ?_⟩
  · rcases ht with rfl | rfl
    · exact Or.inl (pow_one z)
    · exact Or.inr (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hz6))
  · rw [e1, hx, ← pow_add, ← pow_mul]
    exact k91np_pow_congr hz6 (by rcases ht with rfl | rfl <;> omega)
  · rw [e2, hy, ← pow_add, ← pow_mul]
    exact k91np_pow_congr hz6 (by rcases ht with rfl | rfl <;> omega)
  · rw [e3, hxy, ← pow_add, ← pow_mul]
    exact k91np_pow_congr hz6 h1
  · rw [e4, hxyy, ← pow_add, ← pow_mul]
    exact k91np_pow_congr hz6 h2

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs
