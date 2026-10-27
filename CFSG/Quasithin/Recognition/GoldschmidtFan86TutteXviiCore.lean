module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.Fan86.Tutte.Xvii

variable {G : Type*} [Group G]

theorem pow_conj_eq {y z : G} (h3 : y ^ 3 * z * y ^ 3 = z) (K : ℕ) :
    y ^ (3 * K) * z * y ^ (3 * K) = z := by
  induction K with
  | zero => simp
  | succ K ih =>
    calc y ^ (3 * (K + 1)) * z * y ^ (3 * (K + 1))
        = y ^ 3 * (y ^ (3 * K) * z * y ^ (3 * K)) * y ^ 3 := by group
      _ = z := by rw [ih, h3]

theorem exists_pow_eq_self {y : G} {N : ℕ} (hy : y ^ (2 ^ N) = 1) : ∃ K : ℕ, y ^ (3 * K) = y := by
  have hcop : Nat.Coprime 3 (orderOf y) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hy)
      (Nat.Coprime.pow_right N (by decide : Nat.Coprime 3 2))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  exact ⟨m, by rw [pow_mul]; exact hm⟩

theorem core {y z e P R : G} {N : ℕ}
    (he : e * e = 1) (hP : P * P = 1) (hR : R * R = 1) (heR : e * R = R * e)
    (hyz : y * z⁻¹ * y = z) (hRy : R * y = y⁻¹ * R) (hPy : P * y = y⁻¹ * P)
    (hey : e * y * e * y = P * z) (hPz : P * z = z⁻¹ * P) (hz2 : z * z = e * R)
    (hord : y ^ (2 ^ N) = 1) : z * z = 1 := by
  have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have hP' : P⁻¹ = P := inv_eq_of_mul_eq_one_right hP
  have hz4 : z * z * (z * z) = 1 := by
    rw [hz2]
    calc e * R * (e * R) = e * (R * e) * R := by group
      _ = e * (e * R) * R := by rw [← heR]
      _ = (e * e) * (R * R) := by group
      _ = 1 := by rw [he, hR, one_mul]
  have h1 : y⁻¹ * e * y⁻¹ = z⁻¹ * P * e := by
    have hye : y * e * y = e * (P * z) := by
      calc y * e * y = e * (e * y * e * y) := by
            calc y * e * y = (e * e) * y * e * y := by rw [he, one_mul]
              _ = e * (e * y * e * y) := by group
        _ = e * (P * z) := by rw [hey]
    calc y⁻¹ * e * y⁻¹ = (y * e⁻¹ * y)⁻¹ := by group
      _ = (y * e * y)⁻¹ := by rw [he']
      _ = (e * (P * z))⁻¹ := by rw [hye]
      _ = z⁻¹ * P * e := by rw [mul_inv_rev, mul_inv_rev, hP', he']
  have h2 : y * z * y = P * e * R := by
    have hQ : y⁻¹ * (z * z) * y = z⁻¹ * P * e * R := by
      rw [hz2]
      calc y⁻¹ * (e * R) * y = y⁻¹ * e * (R * y) := by group
        _ = y⁻¹ * e * (y⁻¹ * R) := by rw [hRy]
        _ = (y⁻¹ * e * y⁻¹) * R := by group
        _ = z⁻¹ * P * e * R := by rw [h1]
    calc y * z * y = (y * z⁻¹ * y) * (y⁻¹ * (z * z) * y) := by group
      _ = z * (z⁻¹ * P * e * R) := by rw [hyz, hQ]
      _ = P * e * R := by group
  have h3 : y * y * z * y * y = z * z * z := by
    have hyP : y * P = P * y⁻¹ := by
      have : y * (P * y) = P := by rw [hPy]; group
      calc y * P = y * (P * y) * y⁻¹ := by group
        _ = P * y⁻¹ := by rw [this]
    have hzP : z * P = P * z⁻¹ := by
      have : z * (P * z) = P := by rw [hPz]; group
      calc z * P = z * (P * z) * z⁻¹ := by group
        _ = P * z⁻¹ := by rw [this]
    calc y * y * z * y * y = y * (y * z * y) * y := by group
      _ = y * (P * e * R) * y := by rw [h2]
      _ = (y * P) * e * (R * y) := by group
      _ = (P * y⁻¹) * e * (y⁻¹ * R) := by rw [hyP, hRy]
      _ = P * (y⁻¹ * e * y⁻¹) * R := by group
      _ = P * (z⁻¹ * P * e) * R := by rw [h1]
      _ = (P * z⁻¹) * P * e * R := by group
      _ = (z * P) * P * e * R := by rw [← hzP]
      _ = z * (P * P) * e * R := by group
      _ = z * 1 * e * R := by rw [hP]
      _ = z * (e * R) := by group
      _ = z * (z * z) := by rw [hz2]
      _ = z * z * z := by group
  have h4 : y ^ 3 * z * y ^ 3 = z := by
    have hz3 : z * z * z = z⁻¹ := by
      have : z * z * z * z = 1 := by rw [← hz4]; group
      exact eq_inv_of_mul_eq_one_left this
    rw [pow_three']
    calc y * y * y * z * (y * y * y) = y * (y * y * z * y * y) * y := by group
      _ = y * (z * z * z) * y := by rw [h3]
      _ = y * z⁻¹ * y := by rw [hz3]
      _ = z := hyz
  obtain ⟨K, hK⟩ := exists_pow_eq_self hord
  have h5 : y * z * y = z := by
    have := pow_conj_eq h4 K
    rwa [hK] at this
  have h6 : y * z * y = y * z⁻¹ * y := h5.trans hyz.symm
  have h7 : z = z⁻¹ := by
    have := mul_right_cancel h6
    exact mul_left_cancel this
  exact mul_eq_one_iff_eq_inv.2 h7

end CFSG.Quasithin.Fan86.Tutte.Xvii
