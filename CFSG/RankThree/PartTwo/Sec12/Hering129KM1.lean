module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.RankThree.PartTwo.Sec12

theorem km1_zpow_mul_zpow {G : Type*} [Group G] {x y ω : G}
    (hω : ∀ g : G, ω * g = g * ω) (hxy : x * y * x⁻¹ * y⁻¹ = ω) (i j : ℤ) :
    x ^ i * y ^ j = ω ^ (i * j) * (y ^ j * x ^ i) := by
  have hc : ∀ g : G, Commute ω g := hω
  have hz : ∀ (k : ℤ) (g : G), ω ^ k * g = g * ω ^ k := fun k g => ((hc g).zpow_left k).eq
  have hxy2 : x * y = ω * y * x := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_iff_eq_mul.mp hxy)
  have h1 : y⁻¹ * x * y = ω * x := by
    calc y⁻¹ * x * y = y⁻¹ * (x * y) := by rw [mul_assoc]
      _ = y⁻¹ * (ω * y * x) := by rw [hxy2]
      _ = y⁻¹ * (y * ω * x) := by rw [hω y]
      _ = ω * x := by simp [mul_assoc]
  have h2 : ∀ k : ℤ, y⁻¹ * x ^ k * y = ω ^ k * x ^ k := fun k => by
    have h := conj_zpow (i := k) (a := y⁻¹) (b := x)
    rw [inv_inv, h1] at h
    rw [← h]
    exact (hc x).mul_zpow k
  have h3 : ∀ k : ℤ, x ^ k * y = ω ^ k * (y * x ^ k) := fun k => by
    calc x ^ k * y = y * (y⁻¹ * x ^ k * y) := by simp [mul_assoc]
      _ = y * (ω ^ k * x ^ k) := by rw [h2 k]
      _ = (y * ω ^ k) * x ^ k := by rw [mul_assoc]
      _ = (ω ^ k * y) * x ^ k := by rw [hz k y]
      _ = ω ^ k * (y * x ^ k) := by rw [mul_assoc]
  have hh : x ^ i * y * (x ^ i)⁻¹ = ω ^ i * y := by
    rw [h3 i]
    simp [mul_assoc]
  have h4 : x ^ i * y ^ j * (x ^ i)⁻¹ = ω ^ (i * j) * y ^ j := by
    calc x ^ i * y ^ j * (x ^ i)⁻¹ = (x ^ i * y * (x ^ i)⁻¹) ^ j := conj_zpow.symm
      _ = (ω ^ i * y) ^ j := by rw [hh]
      _ = (ω ^ i) ^ j * y ^ j := ((hc y).zpow_left i).mul_zpow j
      _ = ω ^ (i * j) * y ^ j := by rw [← zpow_mul]
  calc x ^ i * y ^ j = ω ^ (i * j) * y ^ j * x ^ i := mul_inv_eq_iff_eq_mul.mp h4
    _ = ω ^ (i * j) * (y ^ j * x ^ i) := mul_assoc _ _ _

theorem km1_mono_comm {G : Type*} [Group G] {x y ω : G}
    (hω : ∀ g : G, ω * g = g * ω) (hxy : x * y * x⁻¹ * y⁻¹ = ω) (a b c d : ℤ) :
    ω ^ (b * c) * (x ^ a * y ^ c * (x ^ b * y ^ d)) =
      ω ^ (a * d) * (x ^ b * y ^ d * (x ^ a * y ^ c)) := by
  have hc : ∀ g : G, Commute ω g := hω
  have K := km1_zpow_mul_zpow hω hxy
  have e1 : ω ^ (b * c) * (x ^ a * y ^ c * (x ^ b * y ^ d)) = x ^ (a + b) * y ^ (c + d) := by
    calc ω ^ (b * c) * (x ^ a * y ^ c * (x ^ b * y ^ d))
        = ω ^ (b * c) * (x ^ a * (y ^ c * x ^ b * y ^ d)) := by simp only [mul_assoc]
      _ = x ^ a * (ω ^ (b * c) * (y ^ c * x ^ b * y ^ d)) :=
          ((hc (x ^ a)).zpow_left (b * c)).left_comm _
      _ = x ^ a * (ω ^ (b * c) * (y ^ c * x ^ b)) * y ^ d := by simp only [mul_assoc]
      _ = x ^ a * (x ^ b * y ^ c) * y ^ d := by rw [← K b c]
      _ = x ^ (a + b) * y ^ (c + d) := by rw [zpow_add, zpow_add]; simp only [mul_assoc]
  have e2 : ω ^ (a * d) * (x ^ b * y ^ d * (x ^ a * y ^ c)) = x ^ (a + b) * y ^ (c + d) := by
    calc ω ^ (a * d) * (x ^ b * y ^ d * (x ^ a * y ^ c))
        = ω ^ (a * d) * (x ^ b * (y ^ d * x ^ a * y ^ c)) := by simp only [mul_assoc]
      _ = x ^ b * (ω ^ (a * d) * (y ^ d * x ^ a * y ^ c)) :=
          ((hc (x ^ b)).zpow_left (a * d)).left_comm _
      _ = x ^ b * (ω ^ (a * d) * (y ^ d * x ^ a)) * y ^ c := by simp only [mul_assoc]
      _ = x ^ b * (x ^ a * y ^ d) * y ^ c := by rw [← K a d]
      _ = x ^ (a + b) * y ^ (c + d) := by
          rw [add_comm a b, add_comm c d, zpow_add, zpow_add]; simp only [mul_assoc]
  rw [e1, e2]

theorem pairing_det_mod_three {G : Type*} [Group G] {x y ω l₁ l₂ m : G} {a b c d : ℤ}
    (hω : ∀ g : G, ω * g = g * ω) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hxy : x * y * x⁻¹ * y⁻¹ = ω)
    (hl₁ : ∀ g : G, l₁ * g = g * l₁) (hl₂ : ∀ g : G, l₂ * g = g * l₂)
    (hm₁ : m * x * m⁻¹ = l₁ * (x ^ a * y ^ c)) (hm₂ : m * y * m⁻¹ = l₂ * (x ^ b * y ^ d)) :
    (a * d - b * c) % 3 = 1 := by
  have hc : ∀ g : G, Commute ω g := hω
  have key := km1_mono_comm hω hxy a b c d
  generalize x ^ a * y ^ c = u at hm₁ key
  generalize x ^ b * y ^ d = v at hm₂ key
  have hxy2 : x * y = ω * y * x := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_iff_eq_mul.mp hxy)
  have hmω : m * ω * m⁻¹ = ω := by rw [← hω m, mul_inv_cancel_right]
  have hconj : (m * x * m⁻¹) * (m * y * m⁻¹) = ω * ((m * y * m⁻¹) * (m * x * m⁻¹)) := by
    calc (m * x * m⁻¹) * (m * y * m⁻¹) = m * (x * y) * m⁻¹ := by simp [mul_assoc]
      _ = m * (ω * y * x) * m⁻¹ := by rw [hxy2]
      _ = (m * ω * m⁻¹) * ((m * y * m⁻¹) * (m * x * m⁻¹)) := by
        simp [mul_assoc]
      _ = ω * ((m * y * m⁻¹) * (m * x * m⁻¹)) := by rw [hmω]
  rw [hm₁, hm₂] at hconj
  have hcomm : u * v = ω * (v * u) := by
    have e1 : l₁ * u * (l₂ * v) = l₁ * l₂ * (u * v) :=
      Commute.mul_mul_mul_comm (show Commute u l₂ from (hl₂ u).symm) l₁ v
    have e2 : l₂ * v * (l₁ * u) = l₂ * l₁ * (v * u) :=
      Commute.mul_mul_mul_comm (show Commute v l₁ from (hl₁ v).symm) l₂ u
    rw [e1, e2, ← hl₁ l₂, (hc (l₁ * l₂)).left_comm] at hconj
    exact mul_left_cancel hconj
  have hEq : ω ^ (b * c + 1) = ω ^ (a * d) := by
    have h : ω ^ (b * c) * (ω * (v * u)) = ω ^ (a * d) * (v * u) := by
      rw [← hcomm, key]
    rw [← mul_assoc] at h
    rw [zpow_add_one]
    exact mul_right_cancel h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  have hdvd : ((orderOf ω : ℕ) : ℤ) ∣ (b * c + 1) - a * d :=
    orderOf_dvd_sub_iff_zpow_eq_zpow.mpr hEq
  rw [hord] at hdvd
  push_cast at hdvd
  omega

end CFSG.RankThree.PartTwo.Sec12
