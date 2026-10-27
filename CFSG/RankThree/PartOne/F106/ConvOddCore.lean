module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartOne.F106
theorem two_pow_le_of_dvd {w c i j m N : ℕ} (hw : Even w) (hw2 : 2 ≤ w) (hi : i ≤ m) (hj : j ≤ m)
    (h : 2 ^ N ∣ 2 ^ c * w ^ i * (w + 2) ^ j) : 2 ^ N ≤ 2 ^ (c + m) * (w + 2) ^ m := by
  obtain ⟨v, rfl⟩ := hw
  have hv : 1 ≤ v := by omega
  rcases Nat.even_or_odd v with hve | hvo
  ·
    have hodd : Odd (v + 1) := hve.add_one
    have hcop : Nat.Coprime (2 ^ N) ((v + 1) ^ j) :=
      (Nat.Coprime.pow_left N (Nat.coprime_two_left.mpr hodd)).pow_right j
    have e : 2 ^ c * (v + v) ^ i * (v + v + 2) ^ j = (2 ^ (c + j) * (v + v) ^ i) * (v + 1) ^ j := by
      have : v + v + 2 = 2 * (v + 1) := by ring
      rw [this, mul_pow, pow_add]; ring
    rw [e] at h
    have h2 := hcop.dvd_of_dvd_mul_right h
    have h3 := Nat.le_of_dvd (by positivity) h2
    refine h3.trans ?_
    calc 2 ^ (c + j) * (v + v) ^ i ≤ 2 ^ (c + m) * (v + v + 2) ^ m := by
          apply Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega))
          calc (v + v) ^ i ≤ (v + v + 2) ^ i := Nat.pow_le_pow_left (by omega) i
            _ ≤ (v + v + 2) ^ m := Nat.pow_le_pow_right (by omega) hi
      _ = _ := rfl
  ·
    have hcop : Nat.Coprime (2 ^ N) (v ^ i) :=
      (Nat.Coprime.pow_left N (Nat.coprime_two_left.mpr hvo)).pow_right i
    have e : 2 ^ c * (v + v) ^ i * (v + v + 2) ^ j = (2 ^ (c + i) * (v + v + 2) ^ j) * v ^ i := by
      have : v + v = 2 * v := by ring
      rw [this, mul_pow, pow_add]; ring
    rw [e] at h
    have h2 := hcop.dvd_of_dvd_mul_right h
    have h3 := Nat.le_of_dvd (by positivity) h2
    refine h3.trans ?_
    apply Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact Nat.pow_le_pow_right (by omega) hj


theorem contra_gen {z M o K A a e : ℕ} (hz : 1 ≤ z) (hM : M ≤ K * z) (hMl : 2 ^ 20 ≤ M)
    (hs : z ^ a ≤ A * o) (ho : o ^ 4 ≤ M ^ 11) (he : 4 * a = e + 11)
    (hnum : A ^ 4 * K ^ (e + 11) < (2 ^ 20) ^ e) : False := by
  have h1 : z ^ (4 * a) ≤ A ^ 4 * M ^ 11 := by
    calc z ^ (4 * a) = (z ^ a) ^ 4 := by rw [mul_comm, pow_mul]
      _ ≤ (A * o) ^ 4 := Nat.pow_le_pow_left hs 4
      _ = A ^ 4 * o ^ 4 := mul_pow _ _ _
      _ ≤ A ^ 4 * M ^ 11 := Nat.mul_le_mul_left _ ho
  have h2 : z ^ e * z ^ 11 ≤ (A ^ 4 * K ^ 11) * z ^ 11 := by
    calc z ^ e * z ^ 11 = z ^ (4 * a) := by rw [← pow_add, he]
      _ ≤ A ^ 4 * M ^ 11 := h1
      _ ≤ A ^ 4 * (K * z) ^ 11 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM 11)
      _ = (A ^ 4 * K ^ 11) * z ^ 11 := by rw [mul_pow]; ring
  have h3 : z ^ e ≤ A ^ 4 * K ^ 11 := Nat.le_of_mul_le_mul_right h2 (by positivity)
  have h4 : (2 ^ 20) ^ e ≤ (K * z) ^ e := Nat.pow_le_pow_left (hMl.trans hM) e
  have h5 : (K * z) ^ e ≤ A ^ 4 * K ^ (e + 11) := by
    calc (K * z) ^ e = K ^ e * z ^ e := mul_pow _ _ _
      _ ≤ K ^ e * (A ^ 4 * K ^ 11) := Nat.mul_le_mul_left _ h3
      _ = A ^ 4 * K ^ (e + 11) := by rw [pow_add]; ring
  exact absurd (h4.trans h5) (not_le.mpr hnum)


theorem odd_family_false {w N : ℕ} (hw2 : 2 ≤ w) (hwe : Even w) (hN : 20 ≤ N)
    {o d X P A c k0 s i j m D a e : ℕ}
    (hod : o * d = X) (hdA : d ≤ A) (hds : 2 ^ s ∣ d) (hP : Odd P)
    (hX : X = P * (2 ^ c * w ^ i * (w + 2) ^ j)) (hk : k0 + s = c + 2 * m) (hlow : w ^ D ≤ X)
    (hi : i ≤ m) (hj : j ≤ m) (hD : D = m * a) (he : 4 * a = e + 11)
    (hnum : A ^ 4 * (2 ^ k0) ^ (e + 11) < (2 ^ 20) ^ e)
    (hdvd : 2 ^ N ∣ o) (hsize : o ^ 4 ≤ (2 ^ N) ^ 11) : False := by
  have h1 : 2 ^ (N + s) ∣ X := by
    rw [pow_add, ← hod]
    exact mul_dvd_mul hdvd hds
  have hcop : Nat.Coprime (2 ^ (N + s)) P :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hP)
  have h2 : 2 ^ (N + s) ∣ 2 ^ c * w ^ i * (w + 2) ^ j := by
    rw [hX] at h1
    exact hcop.dvd_of_dvd_mul_left h1
  have h3 := two_pow_le_of_dvd hwe hw2 hi hj h2
  have h4 : 2 ^ N * 2 ^ s ≤ 2 ^ k0 * w ^ m * 2 ^ s := by
    calc 2 ^ N * 2 ^ s = 2 ^ (N + s) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (c + m) * (w + 2) ^ m := h3
      _ ≤ 2 ^ (c + m) * (2 * w) ^ m := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) m)
      _ = 2 ^ (k0 + s) * w ^ m := by
          rw [mul_pow, hk, ← mul_assoc, ← pow_add]; ring_nf
      _ = 2 ^ k0 * w ^ m * 2 ^ s := by rw [pow_add]; ring
  have h5 : 2 ^ N ≤ 2 ^ k0 * w ^ m := Nat.le_of_mul_le_mul_right h4 (by positivity)
  have h6 : (w ^ m) ^ a ≤ A * o := by
    calc (w ^ m) ^ a = w ^ D := by rw [hD, ← pow_mul]
      _ ≤ X := hlow
      _ = o * d := hod.symm
      _ ≤ o * A := Nat.mul_le_mul_left _ hdA
      _ = A * o := mul_comm _ _
  exact contra_gen (Nat.one_le_pow _ _ (by omega)) h5 (Nat.pow_le_pow_right (by norm_num) hN) h6
    hsize he hnum

end CFSG.RankThree.PartOne.F106
