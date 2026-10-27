module

public import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Basic
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE4

variable {Q : Type*} [CommGroup Q]

theorem map_mem_range_powMonoidHom (α : MulAut Q) {n : ℕ} {x : Q}
    (hx : x ∈ (powMonoidHom n : Q →* Q).range) : α x ∈ (powMonoidHom n : Q →* Q).range := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨α y, by rw [powMonoidHom_apply, powMonoidHom_apply, map_pow]⟩

theorem mul_inv_mem_range_pow_succ {p m j : ℕ} (hj : 1 ≤ j) (hpm : Nat.Coprime m p)
    (α : MulAut Q) (hα : α ^ m = 1)
    (hJ : ∀ x : Q, α x * x⁻¹ ∈ (powMonoidHom (p ^ j) : Q →* Q).range) (x : Q) :
    α x * x⁻¹ ∈ (powMonoidHom (p ^ (j + 1)) : Q →* Q).range := by
  set N := (powMonoidHom (p ^ (j + 1)) : Q →* Q).range with hN
  obtain ⟨y, hy⟩ := hJ x
  rw [powMonoidHom_apply] at hy
  obtain ⟨z, hz⟩ := hJ y
  rw [powMonoidHom_apply] at hz
  have hαy : α y = z ^ p ^ j * y := by rw [hz, inv_mul_cancel_right]
  have hαx : α x = y ^ p ^ j * x := by rw [hy, inv_mul_cancel_right]
  have hαβ : α (y ^ p ^ j) = z ^ (p ^ j * p ^ j) * y ^ p ^ j := by
    rw [map_pow, hαy, mul_pow, ← pow_mul]
  have hn₁ : z ^ (p ^ j * p ^ j) ∈ N := ⟨z ^ p ^ (j - 1), by
    rw [powMonoidHom_apply, ← pow_mul, ← pow_add, ← pow_add]
    congr 2
    omega⟩
  have hk : ∀ k : ℕ, ∃ n ∈ N, (α ^ k) x = (y ^ p ^ j) ^ k * x * n := by
    intro k
    induction k with
    | zero => exact ⟨1, one_mem _, by rw [pow_zero, pow_zero, MulAut.one_apply, one_mul, mul_one]⟩
    | succ k ih =>
      obtain ⟨n, hn, hkx⟩ := ih
      refine ⟨(z ^ (p ^ j * p ^ j)) ^ k * α n, mul_mem (pow_mem hn₁ k)
        (map_mem_range_powMonoidHom α hn), ?_⟩
      rw [pow_succ', MulAut.mul_apply, hkx, map_mul, map_mul, map_pow, hαβ, hαx, mul_pow,
        pow_succ]
      simp only [mul_assoc, mul_comm]
  obtain ⟨n, hn, hm⟩ := hk m
  rw [hα, MulAut.one_apply] at hm
  have hβm : (y ^ p ^ j) ^ m ∈ N := by
    have e : (y ^ p ^ j) ^ m = n⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc (y ^ p ^ j) ^ m * n = x⁻¹ * ((y ^ p ^ j) ^ m * x * n) := by
            rw [mul_comm ((y ^ p ^ j) ^ m) x, mul_assoc, inv_mul_cancel_left]
        _ = 1 := by rw [← hm, inv_mul_cancel]
    rw [e]
    exact inv_mem hn
  have hβp : (y ^ p ^ j) ^ p ∈ N := ⟨y, by rw [powMonoidHom_apply, ← pow_mul, ← pow_succ]⟩
  rw [← hy]
  exact EmptyFaithfulMultiple.L3213.mem_of_pow_mem_of_pow_mem hpm hβm hβp

theorem apply_eq_of_mul_inv_mem_range_pow {p a m : ℕ} (hpm : Nat.Coprime m p)
    (hexp : ∀ x : Q, x ^ p ^ a = 1) (α : MulAut Q) (hα : α ^ m = 1)
    (h1 : ∀ x : Q, α x * x⁻¹ ∈ (powMonoidHom p : Q →* Q).range) (x : Q) : α x = x := by
  have key : ∀ j, 1 ≤ j → ∀ x : Q, α x * x⁻¹ ∈ (powMonoidHom (p ^ j) : Q →* Q).range := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => simpa using h1
    | succ j hj ih => exact mul_inv_mem_range_pow_succ hj hpm α hα ih
  rcases Nat.eq_zero_or_pos a with ha | ha
  · have h0 : ∀ y : Q, y = 1 := fun y => by simpa [ha] using hexp y
    rw [h0 (α x), h0 x]
  obtain ⟨y, hy⟩ := key a ha x
  rw [powMonoidHom_apply, hexp] at hy
  exact (mul_inv_eq_one.mp hy.symm)

end CFSG.Quasithin.Vol2.Ch11.OE4
