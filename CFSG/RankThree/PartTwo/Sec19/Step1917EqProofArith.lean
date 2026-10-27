module

public import CFSG.RankThree.PartTwo.Sec4.Statements
import CFSG.RankThree.PartTwo.Sec19.Step1917StepsOrders
import CFSG.RankThree.PartTwo.KFacts.K72SLPiIdent

public section

namespace CFSG.RankThree.PartTwo.Sec19.Step1917EqProof

open CFSG.Open (ordTrialityD4)

theorem sl3Order_lt_su3Order {x : ℕ} (hx : 2 ≤ x) :
    x ^ 3 * (x ^ 2 - 1) * (x ^ 3 - 1) < x ^ 3 * (x ^ 2 - 1) * (x ^ 3 + 1) := by
  have h3 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h2 : 4 ≤ x ^ 2 := by nlinarith
  have hpos : 0 < x ^ 3 * (x ^ 2 - 1) := Nat.mul_pos (by omega) (by omega)
  exact Nat.mul_lt_mul_of_pos_left (by omega) hpos

theorem su3Order_lt_sl3Order_succ {x : ℕ} (hx : 1 ≤ x) :
    x ^ 3 * (x ^ 2 - 1) * (x ^ 3 + 1) <
      (x + 1) ^ 3 * ((x + 1) ^ 2 - 1) * ((x + 1) ^ 3 - 1) := by
  have h2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx
  have e1 : (x + 1) ^ 2 - 1 = x ^ 2 + 2 * x := by
    have : (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by ring
    omega
  have e2 : (x + 1) ^ 3 - 1 = x ^ 3 + 3 * x ^ 2 + 3 * x := by
    have : (x + 1) ^ 3 = x ^ 3 + 3 * x ^ 2 + 3 * x + 1 := by ring
    omega
  rw [e1, e2]
  have a1 : x ^ 3 < (x + 1) ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have a2 : x ^ 2 - 1 < x ^ 2 + 2 * x := by omega
  have a3 : x ^ 3 + 1 ≤ x ^ 3 + 3 * x ^ 2 + 3 * x := by nlinarith
  calc x ^ 3 * (x ^ 2 - 1) * (x ^ 3 + 1)
      < (x + 1) ^ 3 * (x ^ 2 + 2 * x) * (x ^ 3 + 1) := by
        apply Nat.mul_lt_mul_of_pos_right _ (by omega)
        exact Nat.mul_lt_mul'' a1 a2
    _ ≤ (x + 1) ^ 3 * (x ^ 2 + 2 * x) * (x ^ 3 + 3 * x ^ 2 + 3 * x) :=
        Nat.mul_le_mul_left _ a3

theorem sl3Order_ne_su3Order {x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y) :
    x ^ 3 * (x ^ 2 - 1) * (x ^ 3 - 1) ≠ y ^ 3 * (y ^ 2 - 1) * (y ^ 3 + 1) := by
  intro h
  rcases Nat.lt_or_ge y x with hxy | hxy
  · have h1 := su3Order_lt_sl3Order_succ (x := y) (by omega)
    have h2 := Step1917Steps.sl3Order_le (x := y + 1) (y := x) (by omega) hxy
    omega
  · have h1 := sl3Order_lt_su3Order hx
    have h2 := Step1917Steps.su3Order_le (x := x) (y := y) (by omega) hxy
    omega

theorem eq_of_isoLThreePi {Y : Type} [Group Y] {p e p' e' : ℕ} [Fact p.Prime] [Fact p'.Prime]
    (he : 1 ≤ e) (he' : 1 ≤ e') (h : Sec4.IsoLThreePi Y p e) (h' : Sec4.IsoLThreePi Y p' e') :
    p ^ e = p' ^ e' := by
  have hp : p.Prime := Fact.out
  have hp' : p'.Prime := Fact.out
  have hQ : 2 ≤ p ^ e := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  have hQ' : 2 ≤ p' ^ e' := hp'.two_le.trans (Nat.le_self_pow (by omega) p')
  set x := p ^ e
  set y := p' ^ e'
  rcases Step1917Steps.three_mul_card_of_isoLThreePi he h with ⟨-, hf, -⟩ | ⟨-, hf⟩ <;>
  rcases Step1917Steps.three_mul_card_of_isoLThreePi he' h' with ⟨-, hf', -⟩ | ⟨-, hf'⟩
  · rcases Nat.lt_trichotomy x y with hxy | hxy | hxy
    · exact absurd (hf.trans hf'.symm) (KFacts.sl3Order_lt (by omega) hxy).ne
    · exact hxy
    · exact absurd (hf'.trans hf.symm) (KFacts.sl3Order_lt (by omega) hxy).ne
  · exact absurd (hf.trans hf'.symm) (sl3Order_ne_su3Order hQ hQ')
  · exact absurd (hf'.trans hf.symm) (sl3Order_ne_su3Order hQ' hQ)
  · rcases Nat.lt_trichotomy x y with hxy | hxy | hxy
    · exact absurd (hf.trans hf'.symm) (KFacts.su3Order_lt (by omega) hxy).ne
    · exact hxy
    · exact absurd (hf'.trans hf.symm) (KFacts.su3Order_lt (by omega) hxy).ne

theorem su3Order_cube_lt {q : ℕ} (hq : 2 ≤ q) :
    (q ^ 3) ^ 3 * ((q ^ 3) ^ 2 - 1) * ((q ^ 3) ^ 3 + 1) < 3 * ordTrialityD4 q := by
  unfold ordTrialityD4
  have h2 : 4 ≤ q ^ 2 := by nlinarith
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have e6 : (q ^ 3) ^ 2 = q ^ 6 := by ring
  have e9 : (q ^ 3) ^ 3 = q ^ 9 := by ring
  rw [e6, e9]
  have hpos : 0 < q ^ 9 * (q ^ 6 - 1) := Nat.mul_pos (Nat.pow_pos (by omega)) (by
    have : 2 ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
    omega)
  have key : q ^ 9 + 1 < 3 * (q ^ 3 * (q ^ 8 + q ^ 4 + 1) * (q ^ 2 - 1)) := by
    have a : q ^ 9 + 1 ≤ q ^ 11 := by
      have : q ^ 11 = q ^ 9 * q ^ 2 := by ring
      have : q ^ 9 * 4 ≤ q ^ 9 * q ^ 2 := Nat.mul_le_mul_left _ h2
      have : 1 ≤ q ^ 9 := Nat.one_le_pow _ _ (by omega)
      omega
    have b : q ^ 11 < 3 * (q ^ 3 * (q ^ 8 + q ^ 4 + 1) * (q ^ 2 - 1)) := by
      have c1 : q ^ 11 ≤ q ^ 3 * q ^ 8 := by ring_nf; exact le_rfl
      have c2 : q ^ 3 * q ^ 8 ≤ q ^ 3 * (q ^ 8 + q ^ 4 + 1) := Nat.mul_le_mul_left _ (by omega)
      have c3 : q ^ 3 * (q ^ 8 + q ^ 4 + 1) * 1 ≤ q ^ 3 * (q ^ 8 + q ^ 4 + 1) * (q ^ 2 - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have c4 : 0 < q ^ 3 * (q ^ 8 + q ^ 4 + 1) := Nat.mul_pos (Nat.pow_pos (by omega))
        (by omega)
      omega
    omega
  calc q ^ 9 * (q ^ 6 - 1) * (q ^ 9 + 1)
      < q ^ 9 * (q ^ 6 - 1) * (3 * (q ^ 3 * (q ^ 8 + q ^ 4 + 1) * (q ^ 2 - 1))) :=
        Nat.mul_lt_mul_of_pos_left key hpos
    _ = 3 * (q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) := by ring

theorem sl3Order_cube_lt {q : ℕ} (hq : 2 ≤ q) :
    (q ^ 3) ^ 3 * ((q ^ 3) ^ 2 - 1) * ((q ^ 3) ^ 3 - 1) < 3 * ordTrialityD4 q := by
  have h3 : 2 ≤ q ^ 3 := le_trans hq (Nat.le_self_pow (by norm_num) q)
  exact (sl3Order_lt_su3Order h3).trans (su3Order_cube_lt hq)

theorem not_dvd_plus {q : ℕ} (hq : 2 ≤ q) :
    ¬ (q ^ 6 + q ^ 3 + 1 ∣ 3 * ((q ^ 8 + q ^ 4 + 1) * (q ^ 2 - 1))) := by
  intro h
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hz : ((q ^ 6 + q ^ 3 + 1 : ℕ) : ℤ) ∣ ((3 * ((q ^ 8 + q ^ 4 + 1) * (q ^ 2 - 1)) : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr h
  push_cast [h1] at hz
  set z : ℤ := (q : ℤ) with hzdef
  have hz2 : (2 : ℤ) ≤ z := by rw [hzdef]; exact_mod_cast hq
  have e : 3 * ((z ^ 8 + z ^ 4 + 1) * (z ^ 2 - 1)) =
      (3 * z ^ 4 - 3 * z ^ 2 - 3 * z + 3) * (z ^ 6 + z ^ 3 + 1) +
        (3 * z ^ 5 - 3 * z ^ 4 - 3 * z ^ 3 + 6 * z ^ 2 + 3 * z - 6) := by ring
  rw [e] at hz
  have hr : (z ^ 6 + z ^ 3 + 1) ∣ (3 * z ^ 5 - 3 * z ^ 4 - 3 * z ^ 3 + 6 * z ^ 2 + 3 * z - 6) :=
    (dvd_add_right (dvd_mul_left _ _)).mp hz
  have hpos : 0 < 3 * z ^ 5 - 3 * z ^ 4 - 3 * z ^ 3 + 6 * z ^ 2 + 3 * z - 6 := by
    have e2 : 3 * z ^ 5 - 3 * z ^ 4 - 3 * z ^ 3 + 6 * z ^ 2 + 3 * z - 6 =
        3 * (z - 1) * (z ^ 4 - z ^ 2 + z + 2) := by ring
    rw [e2]
    have a : 0 < z - 1 := by linarith
    have b : 0 < z ^ 4 - z ^ 2 + z + 2 := by nlinarith
    positivity
  have hle := Int.le_of_dvd hpos hr
  nlinarith [pow_pos (by linarith : (0 : ℤ) < z) 3, pow_pos (by linarith : (0 : ℤ) < z) 4,
    pow_pos (by linarith : (0 : ℤ) < z) 5, sq_nonneg (z - 3), mul_pos (by linarith : (0 : ℤ) < z)
      (by linarith : (0 : ℤ) < z)]

theorem not_dvd_minus {q : ℕ} (hq : 2 ≤ q) :
    ¬ (q ^ 6 - q ^ 3 + 1 ∣ 3 * ((q ^ 8 + q ^ 4 + 1) * (q ^ 2 - 1))) := by
  intro h
  rcases Nat.lt_or_ge q 4 with h4 | h4
  · interval_cases q <;> norm_num at h
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h36 : q ^ 3 ≤ q ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hz : ((q ^ 6 - q ^ 3 + 1 : ℕ) : ℤ) ∣ ((3 * ((q ^ 8 + q ^ 4 + 1) * (q ^ 2 - 1)) : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr h
  push_cast [h1, h36] at hz
  set z : ℤ := (q : ℤ) with hzdef
  have hz4 : (4 : ℤ) ≤ z := by rw [hzdef]; exact_mod_cast h4
  have e : 3 * ((z ^ 8 + z ^ 4 + 1) * (z ^ 2 - 1)) =
      (3 * z ^ 4 - 3 * z ^ 2 + 3 * z + 3) * (z ^ 6 - z ^ 3 + 1) -
        (3 * z ^ 5 + 3 * z ^ 4 - 3 * z ^ 3 - 6 * z ^ 2 + 3 * z + 6) := by ring
  rw [e] at hz
  have hr : (z ^ 6 - z ^ 3 + 1) ∣ (3 * z ^ 5 + 3 * z ^ 4 - 3 * z ^ 3 - 6 * z ^ 2 + 3 * z + 6) :=
    (dvd_sub_right (dvd_mul_left _ _)).mp hz
  have hpos : 0 < 3 * z ^ 5 + 3 * z ^ 4 - 3 * z ^ 3 - 6 * z ^ 2 + 3 * z + 6 := by
    have e2 : 3 * z ^ 5 + 3 * z ^ 4 - 3 * z ^ 3 - 6 * z ^ 2 + 3 * z + 6 =
        3 * (z + 1) * (z ^ 4 - z ^ 2 - z + 2) := by ring
    rw [e2]
    have a : 0 < z + 1 := by linarith
    have b : 0 < z ^ 4 - z ^ 2 - z + 2 := by nlinarith
    positivity
  have hle := Int.le_of_dvd hpos hr
  nlinarith [pow_pos (by linarith : (0 : ℤ) < z) 3, pow_pos (by linarith : (0 : ℤ) < z) 4,
    pow_pos (by linarith : (0 : ℤ) < z) 5, mul_pos (by linarith : (0 : ℤ) < z)
      (by linarith : (0 : ℤ) < z), sq_nonneg (z - 4)]

theorem not_dvd_ordTrialityD4 {q N : ℕ} (hq : 2 ≤ q)
    (hN : 3 * N = (q ^ 3) ^ 3 * ((q ^ 3) ^ 2 - 1) * ((q ^ 3) ^ 3 - 1) ∨
      3 * N = (q ^ 3) ^ 3 * ((q ^ 3) ^ 2 - 1) * ((q ^ 3) ^ 3 + 1)) :
    ¬ N ∣ ordTrialityD4 q := by
  intro hdvd
  unfold ordTrialityD4 at hdvd
  have e6 : (q ^ 3) ^ 2 = q ^ 6 := by ring
  have e9 : (q ^ 3) ^ 3 = q ^ 9 := by ring
  rw [e6, e9] at hN
  have h6 : 2 ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
  have hpos : 0 < q ^ 9 * (q ^ 6 - 1) := Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
  have h3 : 3 * N ∣ 3 * (q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) :=
    Nat.mul_dvd_mul_left 3 hdvd
  have hT : 3 * (q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) =
      q ^ 9 * (q ^ 6 - 1) * (q ^ 3 * (3 * ((q ^ 8 + q ^ 4 + 1) * (q ^ 2 - 1)))) := by ring
  rw [hT] at h3
  have hcop : ∀ Φ : ℕ, Φ % q = 1 → Nat.Coprime Φ (q ^ 3) := by
    intro Φ hΦ
    apply Nat.Coprime.pow_right
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hΦ, Nat.gcd_one_left]
  rcases hN with hN | hN
  · rw [hN] at h3
    have h9 := Nat.dvd_of_mul_dvd_mul_left hpos h3
    have hΦ : q ^ 6 + q ^ 3 + 1 ∣ q ^ 9 - 1 := by
      have e : q ^ 9 - 1 = (q ^ 3 - 1) * (q ^ 6 + q ^ 3 + 1) := by
        have h31 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
        zify [h31, Nat.one_le_pow 9 q (by omega)]
        ring
      rw [e]
      exact dvd_mul_left _ _
    have hm : (q ^ 6 + q ^ 3 + 1) % q = 1 := by
      have e : q ^ 6 + q ^ 3 + 1 = 1 + q * (q ^ 5 + q ^ 2) := by ring
      rw [e, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    exact not_dvd_plus hq ((hcop _ hm).dvd_of_dvd_mul_left (hΦ.trans h9))
  · rw [hN] at h3
    have h9 := Nat.dvd_of_mul_dvd_mul_left hpos h3
    have h36 : q ^ 3 ≤ q ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have hΦ : q ^ 6 - q ^ 3 + 1 ∣ q ^ 9 + 1 := by
      have e : q ^ 9 + 1 = (q ^ 3 + 1) * (q ^ 6 - q ^ 3 + 1) := by
        zify [h36]
        ring
      rw [e]
      exact dvd_mul_left _ _
    have hm : (q ^ 6 - q ^ 3 + 1) % q = 1 := by
      have e : q ^ 6 - q ^ 3 + 1 = 1 + q * (q ^ 5 - q ^ 2) := by
        have h25 : q ^ 2 ≤ q ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
        zify [h36, h25]
        ring
      rw [e, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    exact not_dvd_minus hq ((hcop _ hm).dvd_of_dvd_mul_left (hΦ.trans h9))

end CFSG.RankThree.PartTwo.Sec19.Step1917EqProof
