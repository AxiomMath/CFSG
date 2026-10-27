module

public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item812Res8

theorem not_dvd_unitary {q : ℕ} (hq : 2 ≤ q) :
    ¬ q ^ 3 * ((q ^ 3) ^ 2 - 1) ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
  intro h
  have h2 : 4 ≤ q ^ 2 := by nlinarith
  have h3 : 8 ≤ q ^ 3 := by nlinarith
  have hpos : 0 < q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
    have : 0 < q ^ 2 - 1 := by omega
    positivity
  have hle := Nat.le_of_dvd hpos h
  have e1 : (q ^ 3) ^ 2 - 1 = (q ^ 3 - 1) * (q ^ 3 + 1) := by
    have : 1 ≤ q ^ 3 := by omega
    zify [this, Nat.one_le_pow 2 (q ^ 3) (by omega)]
    ring
  rw [e1] at hle
  have hlt : q ^ 2 - 1 < q ^ 3 - 1 := by
    have : q ^ 2 < q ^ 3 := by
      calc q ^ 2 < q ^ 2 * q := by nlinarith
        _ = q ^ 3 := by ring
    omega
  have : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) < q ^ 3 * ((q ^ 3 - 1) * (q ^ 3 + 1)) := by
    rw [← mul_assoc]
    apply Nat.mul_lt_mul_of_pos_right _ (by omega)
    exact Nat.mul_lt_mul_of_pos_left hlt (by positivity)
  omega

theorem not_dvd_linear {q : ℕ} (hq : 2 ≤ q) :
    ¬ q ^ 3 * ((q ^ 3) ^ 2 - 1) ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) := by
  intro h
  have h2 : 4 ≤ q ^ 2 := by nlinarith
  have h3 : 8 ≤ q ^ 3 := by nlinarith
  have hpos : 0 < q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) := by
    have : 0 < q ^ 2 - 1 := by omega
    have : 0 < q ^ 3 - 1 := by omega
    positivity
  have hle := Nat.le_of_dvd hpos h
  have e1 : (q ^ 3) ^ 2 - 1 = (q ^ 3 - 1) * (q ^ 3 + 1) := by
    have : 1 ≤ q ^ 3 := by omega
    zify [this, Nat.one_le_pow 2 (q ^ 3) (by omega)]
    ring
  rw [e1] at hle
  have hq23 : q ^ 2 ≤ q ^ 3 := by
    calc q ^ 2 ≤ q ^ 2 * q := Nat.le_mul_of_pos_right _ (by omega)
      _ = q ^ 3 := by ring
  have hlt : q ^ 2 - 1 < q ^ 3 + 1 := by omega
  have ea : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) = (q ^ 3 * (q ^ 3 - 1)) * (q ^ 2 - 1) := by ring
  have eb : q ^ 3 * ((q ^ 3 - 1) * (q ^ 3 + 1)) = (q ^ 3 * (q ^ 3 - 1)) * (q ^ 3 + 1) := by
    ring
  have hp : 0 < q ^ 3 * (q ^ 3 - 1) := by
    have : 0 < q ^ 3 - 1 := by omega
    positivity
  have := Nat.mul_lt_mul_of_pos_left hlt hp
  rw [ea, eb] at hle
  omega

theorem coprime_of_comb {a b : ℕ} (u v : ℤ) (h : u * a + v * b = 1) : Nat.Coprime a b :=
  Nat.isCoprime_iff_coprime.mp ⟨u, v, h⟩

theorem not_dvd_symplectic {q : ℕ} (hq : 2 ≤ q) :
    ¬ q ^ 3 * ((q ^ 3) ^ 2 - 1) ∣ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  intro h
  have h2 : 4 ≤ q ^ 2 := by nlinarith
  have h4 : 16 ≤ q ^ 4 := by nlinarith
  have e1 : (q ^ 3) ^ 2 - 1 = (q ^ 2 - 1) * (q ^ 4 + q ^ 2 + 1) := by
    have : 1 ≤ (q ^ 3) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    zify [this, (by omega : 1 ≤ q ^ 2)]
    ring
  have e2 : q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) =
      (q ^ 3 * (q ^ 2 - 1)) * (q * (q ^ 4 - 1)) := by ring
  rw [e1, e2, ← mul_assoc] at h
  have hd := Nat.dvd_of_mul_dvd_mul_left (by
    have : 0 < q ^ 2 - 1 := by omega
    positivity) h
  have hcop : Nat.Coprime (q ^ 4 + q ^ 2 + 1) q :=
    coprime_of_comb 1 (-((q : ℤ) ^ 3 + q)) (by push_cast; ring)
  have hd' := hcop.dvd_of_dvd_mul_left hd
  have hpos : 0 < q ^ 4 - 1 := by omega
  have := Nat.le_of_dvd hpos hd'
  omega

theorem ne_g2 {q : ℕ} (hq : 2 ≤ q) :
    q ^ 3 * ((q ^ 3) ^ 2 - 1) ≠ q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) := by
  intro h
  have h2 : 4 ≤ q ^ 2 := by nlinarith
  have h3 : 8 ≤ q ^ 3 := by nlinarith
  have e : (q ^ 3) ^ 2 = q ^ 6 := by ring
  rw [e] at h
  have h6 : 64 ≤ q ^ 6 := by nlinarith
  have hpos : 0 < q ^ 6 - 1 := by omega
  have e6 : q ^ 6 = q ^ 3 * q ^ 3 := by ring
  have : q ^ 3 * (q ^ 6 - 1) < q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) := by
    have h1 : q ^ 3 * (q ^ 6 - 1) < q ^ 6 * (q ^ 6 - 1) := by
      apply Nat.mul_lt_mul_of_pos_right _ hpos
      rw [e6]; nlinarith
    calc q ^ 3 * (q ^ 6 - 1) < q ^ 6 * (q ^ 6 - 1) := h1
      _ ≤ q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem not_dvd_ree {q : ℕ} (hq : 2 ≤ q) :
    ¬ (q ^ 3) ^ 3 * ((q ^ 3) ^ 2 - 1) * ((q ^ 3) ^ 3 + 1) ∣
      q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) *
        (q ^ 4 - q ^ 2 + 1) := by
  intro h
  have h1q : 1 ≤ q := by omega
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have h2 : 4 ≤ q ^ 2 := by nlinarith
  have hq24 : q ^ 2 ≤ q ^ 4 := by nlinarith
  have h3 : q ^ 3 ≤ q ^ 6 := by nlinarith [pow_le_pow_right₀ h1q (by norm_num : 3 ≤ 6)]
  set P := q ^ 6 - q ^ 3 + 1 with hP
  have hP9 : P ∣ (q ^ 3) ^ 3 + 1 := ⟨q ^ 3 + 1, by
    rw [hP]; zify [h3]; ring⟩
  have hPN : P ∣ q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) *
      (q ^ 4 - q ^ 2 + 1) := (hP9.trans (Dvd.intro_left _ rfl)).trans h
  have cq : Nat.Coprime P q := coprime_of_comb 1 (-((q : ℤ) ^ 5 - q ^ 2)) (by
    rw [hP]; push_cast [h3]; ring)
  have cq1 : Nat.Coprime P (q - 1) := coprime_of_comb 1 (-((q : ℤ) ^ 5 + q ^ 4 + q ^ 3)) (by
    rw [hP]; push_cast [h3, h1q]; ring)
  have cq2 : Nat.Coprime P (q ^ 2 + 1) :=
    coprime_of_comb (-(q : ℤ)) ((q : ℤ) ^ 5 - q ^ 3 - q ^ 2 + q + 1) (by
      rw [hP]; push_cast [h3]; ring)
  have cq4 : Nat.Coprime P (q ^ 4 - q ^ 2 + 1) :=
    coprime_of_comb ((q : ℤ) ^ 3) (-((q : ℤ) ^ 5 + q ^ 3 - q ^ 2 - 1)) (by
      rw [hP]; push_cast [h3, hq24]; ring)
  have h4 := cq4.dvd_of_dvd_mul_right hPN
  have h5 : P ∣ q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) := h4
  have h6 : P ∣ (q + 1) ^ 2 * (q ^ 2 - q + 1) := by
    have e : q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) =
        ((q + 1) ^ 2 * (q ^ 2 - q + 1)) * (q ^ 12 * (q - 1) ^ 2 * (q ^ 2 + 1) ^ 2) := by ring
    rw [e] at h5
    refine (Nat.Coprime.dvd_of_dvd_mul_right ?_ h5)
    exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (cq.pow_right 12) (cq1.pow_right 2))
      (cq2.pow_right 2)
  have hpos : 0 < (q + 1) ^ 2 * (q ^ 2 - q + 1) := by positivity
  have hle := Nat.le_of_dvd hpos h6
  have e7 : (q + 1) ^ 2 * (q ^ 2 - q + 1) = q ^ 4 + q ^ 3 + q + 1 := by
    zify [hq2]; ring
  rw [e7, hP] at hle
  have : q ^ 4 + 2 * q ^ 3 + q < q ^ 6 := by
    nlinarith [pow_le_pow_right₀ h1q (by norm_num : 4 ≤ 6)]
  omega

theorem two_le_two_pow {m : ℕ} (hm : 1 ≤ m) : 2 ≤ 2 ^ m :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

end CFSG.RankThree.PartTwo.Sec8.Item812Res8
