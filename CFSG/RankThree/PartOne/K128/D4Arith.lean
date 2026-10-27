module

public import CFSG.RankThree.PartOne.KF.F128Order

public section

namespace CFSG.RankThree.PartOne.K128

@[expose] def phiNat : ℕ → ℕ → ℕ
  | 1, Q => Q - 1
  | 2, Q => Q + 1
  | 3, Q => Q ^ 2 + Q + 1
  | 6, Q => Q ^ 2 - Q + 1
  | _, _ => 0

theorem cube_add_one_eq (x : ℕ) (hx : 1 ≤ x) : x ^ 3 + 1 = (x + 1) * (x ^ 2 - x + 1) := by
  obtain ⟨w, rfl⟩ : ∃ w, x = w + 1 := ⟨x - 1, by omega⟩
  have h : (w + 1) ^ 2 = (w + 1) + (w * (w + 1)) := by ring
  have h2 : (w + 1) ^ 2 - (w + 1) = w * (w + 1) := by omega
  rw [h2]
  ring

theorem not_dvd_succ_of_dvd_phi6 {p x : ℕ} (hp5 : 5 ≤ p) (hx : 2 ≤ x) (h : p ∣ x ^ 2 - x + 1) :
    ¬ p ∣ x + 1 := by
  intro h1
  have h3 : x ^ 2 - x + 1 = (x + 1) * (x - 2) + 3 := by
    obtain ⟨w, rfl⟩ : ∃ w, x = w + 2 := ⟨x - 2, by omega⟩
    have h : (w + 2) ^ 2 = (w + 2) + ((w + 3) * w + 2) := by ring
    have h2 : (w + 2) ^ 2 - (w + 2) = (w + 3) * w + 2 := by omega
    simp only [h2, Nat.add_sub_cancel]
  rw [h3] at h
  have h4 : p ∣ 3 := (Nat.dvd_add_right (h1.mul_right _)).1 h
  have := Nat.le_of_dvd (by norm_num) h4
  omega

theorem not_dvd_phi6_of_dvd_succ {p x : ℕ} (hp5 : 5 ≤ p) (hx : 2 ≤ x) (h : p ∣ x + 1) :
    ¬ p ∣ x ^ 2 - x + 1 := fun h' => not_dvd_succ_of_dvd_phi6 hp5 hx h' h

theorem factorization_cube_add_one {p q : ℕ} (hp5 : 5 ≤ p) (hq : 2 ≤ q) (h : p ∣ q + 1) :
    (q ^ 3 + 1).factorization p = (q + 1).factorization p := by
  have hnd := not_dvd_phi6_of_dvd_succ hp5 hq h
  have hne : q ^ 2 - q + 1 ≠ 0 := by omega
  rw [cube_add_one_eq q (by omega), Nat.factorization_mul (by omega) hne, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]

theorem cast_phiNat_pow {p q m : ℕ} [Fact p.Prime] (hq : 1 ≤ q)
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6) :
    ((phiNat m (q ^ p) : ℕ) : ZMod p) = ((phiNat m q : ℕ) : ZMod p) := by
  have h1 : 1 ≤ q ^ p := Nat.one_le_pow _ _ hq
  have h2 : q ^ p ≤ (q ^ p) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h3 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) _
  have hf : ((q : ZMod p)) ^ p = q := ZMod.pow_card _
  rcases hm with rfl | rfl | rfl | rfl
  · simp only [phiNat]
    rw [Nat.cast_sub h1, Nat.cast_sub hq]
    push_cast
    rw [hf]
  · simp only [phiNat]
    push_cast
    rw [hf]
  · simp only [phiNat]
    push_cast
    rw [hf]
  · simp only [phiNat]
    rw [Nat.cast_add, Nat.cast_sub h2, Nat.cast_add, Nat.cast_sub h3]
    push_cast
    rw [hf]

theorem dvd_phiNat_of_dvd_pow {p q m : ℕ} (hp : p.Prime) (hq : 1 ≤ q)
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6) (h : p ∣ phiNat m (q ^ p)) : p ∣ phiNat m q := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_zero_iff] at h ⊢
  rwa [← cast_phiNat_pow (p := p) hq hm]

theorem factorization_phi6_pow {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (h : p ∣ q ^ 2 - q + 1) :
    ((q ^ p) ^ 2 - q ^ p + 1).factorization p = (q ^ 2 - q + 1).factorization p + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hQ : 2 ≤ q ^ p := by
    calc 2 ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ p := Nat.pow_le_pow_right (by omega) hp.one_lt.le
  have hnd1 : ¬ p ∣ q + 1 := not_dvd_succ_of_dvd_phi6 hp5 hq h
  have hnd2 : ¬ p ∣ q ^ p + 1 := by
    intro h'
    apply hnd1
    rw [← ZMod.natCast_eq_zero_iff] at h' ⊢
    push_cast at h' ⊢
    rwa [ZMod.pow_card] at h'
  have hq3 : ¬ p ∣ q ^ 3 := fun h' => hpq (hp.dvd_of_dvd_pow h')
  have hc : p ∣ q ^ 3 + 1 := by
    rw [cube_add_one_eq q (by omega)]
    exact dvd_mul_of_dvd_right h _
  have e1 := factorization_pow_add_one hp hp2 hq3
  simp only [hc, ↓reduceIte] at e1
  have hne1 : q ^ 2 - q + 1 ≠ 0 := by omega
  have hne2 : (q ^ p) ^ 2 - q ^ p + 1 ≠ 0 := by
    have : 2 ≤ (q ^ p) ^ 2 := by nlinarith
    omega
  have f1 : (q ^ 3 + 1).factorization p = (q ^ 2 - q + 1).factorization p := by
    rw [cube_add_one_eq q (by omega), Nat.factorization_mul (by omega) hne1, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd1, zero_add]
  have f2 : ((q ^ p) ^ 3 + 1).factorization p = ((q ^ p) ^ 2 - q ^ p + 1).factorization p := by
    rw [cube_add_one_eq (q ^ p) (by omega), Nat.factorization_mul (by omega) hne2,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnd2, zero_add]
  have e2 : (q ^ p) ^ 3 + 1 = (q ^ 3) ^ p + 1 := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [← f2, e2, e1, f1]

theorem factorization_phiNat_pow {p q m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6) (h : p ∣ phiNat m q) :
    (phiNat m (q ^ p)).factorization p = (phiNat m q).factorization p + 1 := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  rcases hm with rfl | rfl | rfl | rfl
  · simp only [phiNat] at h ⊢
    have := factorization_pow_sub_one hp hp2 hq hpq
    simpa [h] using this
  · simp only [phiNat] at h ⊢
    have := factorization_pow_add_one hp hp2 hpq
    simpa [h] using this
  · simp only [phiNat] at h ⊢
    have := factorization_phi3_pow hp hp2 hp3 hq hpq
    simpa [h] using this
  · simp only [phiNat] at h ⊢
    exact factorization_phi6_pow hp hp5 hq hpq h

end CFSG.RankThree.PartOne.K128
