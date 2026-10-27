module

public import CFSG.Quasithin.Background.B69Par
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.ClassicalOrders

namespace B69

theorem two_pow_dvd_of_odd_mul {k a b : ℕ} (hb : Odd b) (h : 2 ^ k ∣ a * b) : 2 ^ k ∣ a :=
  (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hb)).dvd_of_dvd_mul_right h

theorem two_pow_dvd_of_odd_mul' {k a b : ℕ} (ha : Odd a) (h : 2 ^ k ∣ a * b) : 2 ^ k ∣ b :=
  (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr ha)).dvd_of_dvd_mul_left h

theorem le_of_two_pow_dvd_sq_sub_one {k Q : ℕ} (hQ : Odd Q) (hQ1 : 1 < Q)
    (h : 2 ^ (k + 1) ∣ Q ^ 2 - 1) : 2 ^ k ≤ Q + 1 := by
  obtain ⟨u, rfl⟩ := hQ
  have hu : 1 ≤ u := by omega
  have e : (2 * u + 1) ^ 2 - 1 = 4 * (u * (u + 1)) := by
    have : (2 * u + 1) ^ 2 = 4 * (u * (u + 1)) + 1 := by ring
    omega
  rw [e] at h
  rcases k with _ | k
  · simp
  · have h2 : 2 ^ k ∣ u * (u + 1) := by
      have h4 : 4 * 2 ^ k ∣ 4 * (u * (u + 1)) := by
        have : 2 ^ (k + 1 + 1) = 4 * 2 ^ k := by ring
        rwa [this] at h
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h4
    rcases Nat.even_or_odd u with he | ho
    · have h3 : 2 ^ k ∣ u := two_pow_dvd_of_odd_mul he.add_one h2
      have := Nat.le_of_dvd (by omega) h3
      calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        _ ≤ 2 * u := by omega
        _ ≤ 2 * u + 1 + 1 := by omega
    · have h3 : 2 ^ k ∣ u + 1 := two_pow_dvd_of_odd_mul' ho h2
      have := Nat.le_of_dvd (by omega) h3
      calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        _ ≤ 2 * (u + 1) := by omega
        _ = 2 * u + 1 + 1 := by ring

theorem psl2_ineq {x Q X g : ℕ} (hx : 4 ≤ x) (hQ : x ^ 6 ≤ Q + 1) (hg : g ≤ 2)
    (h : X * g + Q = Q ^ 3) : x ^ 6 * ((x ^ 6 - 1) * (x ^ 2 - 1)) < X := by
  have hu : 16 ≤ x ^ 2 := by nlinarith
  have hM3 : x ^ 6 = (x ^ 2) ^ 3 := by ring
  set u := x ^ 2 with hudef
  set M := x ^ 6 with hMdef
  have hM : 4096 ≤ M := by
    rw [hM3]
    calc 4096 = 16 ^ 3 := by norm_num
      _ ≤ u ^ 3 := Nat.pow_le_pow_left hu 3
  have hQ1 : 4095 ≤ Q := by omega
  have h2Q : M ≤ 2 * Q := by omega
  have h4Q : 4 * Q ≤ Q ^ 3 := by
    have hQ2 : 4 ≤ Q ^ 2 := by nlinarith
    calc 4 * Q ≤ Q ^ 2 * Q := Nat.mul_le_mul_right Q hQ2
      _ = Q ^ 3 := by ring
  have hX8 : 3 * Q ^ 3 ≤ 8 * X := by
    have : X * g ≤ X * 2 := Nat.mul_le_mul_left _ hg
    omega
  have hM3le : M ^ 3 ≤ 8 * Q ^ 3 := by
    calc M ^ 3 ≤ (2 * Q) ^ 3 := Nat.pow_le_pow_left h2Q 3
      _ = 8 * Q ^ 3 := by ring
  have hN : M * ((M - 1) * (u - 1)) ≤ M * (M * u) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))
  have key : 64 * (M * (M * u)) < 3 * M ^ 3 := by
    have h64 : 64 * u < 3 * M := by
      rw [hM3]
      have h1 : 256 * u ≤ u * u * u :=
        calc 256 * u = (16 * 16) * u := by norm_num
          _ ≤ (u * u) * u := Nat.mul_le_mul_right _ (Nat.mul_le_mul hu hu)
      have e : u ^ 3 = u * u * u := by ring
      omega
    calc 64 * (M * (M * u)) = M * M * (64 * u) := by ring
      _ < M * M * (3 * M) := Nat.mul_lt_mul_of_pos_left h64 (by positivity)
      _ = 3 * M ^ 3 := by ring
  omega

theorem sz_ineq {x Q : ℕ} (hx : 4 ≤ x) (hQ : x ^ 3 ≤ Q) :
    x ^ 6 * ((x ^ 6 - 1) * (x ^ 2 - 1)) < Q ^ 2 * (Q ^ 2 + 1) * (Q - 1) := by
  have hx2 : x ^ 2 + 1 ≤ x ^ 3 := by nlinarith
  have hM : x ^ 6 ≤ Q ^ 2 := by
    calc x ^ 6 = (x ^ 3) ^ 2 := by ring
      _ ≤ Q ^ 2 := Nat.pow_le_pow_left hQ 2
  have hx16 : 16 ≤ x ^ 2 := by nlinarith
  have hu : x ^ 2 ≤ Q - 1 := by omega
  have hN : x ^ 6 * ((x ^ 6 - 1) * (x ^ 2 - 1)) ≤ x ^ 6 * (x ^ 6 * x ^ 2) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))
  have h1 : x ^ 6 * (x ^ 6 * x ^ 2) ≤ Q ^ 2 * Q ^ 2 * (Q - 1) := by
    calc x ^ 6 * (x ^ 6 * x ^ 2) = x ^ 6 * x ^ 6 * x ^ 2 := by ring
      _ ≤ Q ^ 2 * Q ^ 2 * (Q - 1) := Nat.mul_le_mul (Nat.mul_le_mul hM hM) hu
  have hpos : 0 < Q ^ 2 * (Q - 1) := by
    have hQ0 : 0 < Q := by omega
    exact Nat.mul_pos (pow_pos hQ0 2) (by omega)
  have h2 : Q ^ 2 * Q ^ 2 * (Q - 1) < Q ^ 2 * (Q ^ 2 + 1) * (Q - 1) := by
    have : Q ^ 2 * (Q ^ 2 + 1) * (Q - 1) = Q ^ 2 * Q ^ 2 * (Q - 1) + Q ^ 2 * (Q - 1) := by ring
    omega
  omega

theorem unit_ineq {x Q g X : ℕ} (hx : 4 ≤ x) (hQ : x ^ 2 ≤ Q) (hg : g ≤ 3)
    (h : X * g = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) ∨
      X * g = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1))) :
    x ^ 6 * ((x ^ 6 - 1) * (x ^ 2 - 1)) < X := by
  have hx1 : 1 ≤ x ^ 2 := by nlinarith
  obtain ⟨v, hv⟩ : ∃ v, x ^ 2 = v + 1 := ⟨x ^ 2 - 1, by omega⟩
  have hv15 : 15 ≤ v := by nlinarith
  have hM : x ^ 6 = (v + 1) ^ 3 := by rw [← hv]; ring
  have hQ3 : x ^ 6 ≤ Q ^ 3 := by
    calc x ^ 6 = (x ^ 2) ^ 3 := by ring
      _ ≤ Q ^ 3 := Nat.pow_le_pow_left hQ 3
  have hQ2 : v * (v + 2) ≤ Q ^ 2 - 1 := by
    have h1 : (x ^ 2) ^ 2 ≤ Q ^ 2 := Nat.pow_le_pow_left hQ 2
    have h2 : (x ^ 2) ^ 2 = v * (v + 2) + 1 := by rw [hv]; ring
    omega
  have hM1 : x ^ 6 - 1 ≤ Q ^ 3 - 1 := Nat.sub_le_sub_right hQ3 1
  have hM1' : x ^ 6 - 1 ≤ Q ^ 3 + 1 := by omega
  have hB : x ^ 6 * ((v * (v + 2)) * (x ^ 6 - 1)) ≤ X * g := by
    rcases h with h | h
    · rw [h]
      exact Nat.mul_le_mul hQ3 (Nat.mul_le_mul hQ2 hM1')
    · rw [h]
      exact Nat.mul_le_mul hQ3 (Nat.mul_le_mul hQ2 hM1)
  have hXg : X * g ≤ X * 3 := Nat.mul_le_mul_left _ hg
  have hNeq : x ^ 6 * ((v * (v + 2)) * (x ^ 6 - 1)) =
      (x ^ 6 * ((x ^ 6 - 1) * (x ^ 2 - 1))) * (v + 2) := by
    have : x ^ 2 - 1 = v := by omega
    rw [this]
    ring
  have hNpos : 0 < x ^ 6 * ((x ^ 6 - 1) * (x ^ 2 - 1)) := by
    have h1 : 0 < x ^ 6 := by positivity
    have h6 : 4 ^ 6 ≤ x ^ 6 := Nat.pow_le_pow_left hx 6
    have h2 : 0 < x ^ 6 - 1 := by norm_num at h6; omega
    have h3 : 0 < x ^ 2 - 1 := by omega
    exact Nat.mul_pos h1 (Nat.mul_pos h2 h3)
  set N := x ^ 6 * ((x ^ 6 - 1) * (x ^ 2 - 1)) with hNdef
  have h17 : N * 17 ≤ N * (v + 2) := Nat.mul_le_mul_left _ (by omega)
  rw [hNeq] at hB
  omega

theorem sp4_ineq {x Q : ℕ} (hx : 4 ≤ x) (hQ : x ^ 3 ≤ Q ^ 2) :
    x ^ 6 * ((x ^ 6 - 1) * (x ^ 2 - 1)) < Q ^ 4 * ((Q ^ 2 - 1) * (Q ^ 4 - 1)) := by
  have hx2 : x ^ 2 + 1 ≤ x ^ 3 := by nlinarith
  have hM : x ^ 6 ≤ Q ^ 4 := by
    calc x ^ 6 = (x ^ 3) ^ 2 := by ring
      _ ≤ (Q ^ 2) ^ 2 := Nat.pow_le_pow_left hQ 2
      _ = Q ^ 4 := by ring
  have hu : x ^ 2 ≤ Q ^ 2 - 1 := by omega
  have hM1 : x ^ 6 - 1 ≤ Q ^ 4 - 1 := Nat.sub_le_sub_right hM 1
  have hpos : 0 < x ^ 6 * (x ^ 6 - 1) := by
    have h1 : 0 < x ^ 6 := by positivity
    have h6 : 4 ^ 6 ≤ x ^ 6 := Nat.pow_le_pow_left hx 6
    have h2 : 0 < x ^ 6 - 1 := by norm_num at h6; omega
    exact Nat.mul_pos h1 h2
  have h1 : x ^ 6 * ((x ^ 6 - 1) * x ^ 2) ≤ Q ^ 4 * ((Q ^ 2 - 1) * (Q ^ 4 - 1)) := by
    calc x ^ 6 * ((x ^ 6 - 1) * x ^ 2) ≤ Q ^ 4 * ((x ^ 6 - 1) * (Q ^ 2 - 1)) :=
          Nat.mul_le_mul hM (Nat.mul_le_mul le_rfl hu)
      _ ≤ Q ^ 4 * ((Q ^ 4 - 1) * (Q ^ 2 - 1)) :=
          Nat.mul_le_mul le_rfl (Nat.mul_le_mul hM1 le_rfl)
      _ = Q ^ 4 * ((Q ^ 2 - 1) * (Q ^ 4 - 1)) := by ring
  have h2 : x ^ 6 * ((x ^ 6 - 1) * (x ^ 2 - 1)) < x ^ 6 * ((x ^ 6 - 1) * x ^ 2) := by
    have hx1 : 1 ≤ x ^ 2 := by nlinarith
    have e : x ^ 6 * ((x ^ 6 - 1) * x ^ 2) =
        x ^ 6 * ((x ^ 6 - 1) * (x ^ 2 - 1)) + x ^ 6 * (x ^ 6 - 1) := by
      have h1 : x ^ 2 = (x ^ 2 - 1) + 1 := by omega
      conv_lhs => rw [h1]
      ring
    omega
  omega

end B69

end CFSG.Quasithin
