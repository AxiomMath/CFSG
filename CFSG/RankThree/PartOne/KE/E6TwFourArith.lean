module

public import CFSG.RankThree.PartOne.KE.E6FourArith
public import CFSG.RankThree.PartOne.KE.CTTwistedArith

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

namespace CTTw

theorem ordProj_twisted_four {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (hord : orderOf (q : ZMod p) = 4) (hx : (q : ZMod p) ^ 2 + 1 = 0) :
    p ^ (q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
        (q ^ 2 - 1)).factorization p = p ^ ((q ^ 2 + 1) ^ 2).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h3 : ((3 : ℕ) : ZMod p) ≠ 0 := CTE6.natCast_ne_zero_of_lt (by norm_num) (by omega)
  have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := CTE6.natCast_ne_zero_of_lt (by norm_num) (by omega)
  have hy4 : (q : ZMod p) ^ 4 = 1 := by linear_combination ((q : ZMod p) ^ 2 - 1) * hx
  have hy8 : (q : ZMod p) ^ 8 = 1 := by linear_combination ((q : ZMod p) ^ 4 + 1) * hy4
  have f2 : (q : ZMod p) ^ 4 + 1 ≠ 0 := fun hc => h2 (by push_cast; linear_combination hc - hy4)
  have f3 : (q : ZMod p) ^ 8 + (q : ZMod p) ^ 4 + 1 ≠ 0 := fun hc =>
    h3 (by push_cast; linear_combination hc - hy8 - hy4)
  have hnd : ∀ y : ℤ, (y : ZMod p) ≠ 0 → ¬ (p : ℤ) ∣ y := fun y hy hd =>
    hy ((ZMod.intCast_zmod_eq_zero_iff_dvd y p).2 hd)
  have hq1 : 1 ≤ q := by omega
  have hn₀ : (q ^ 2 + 1) ^ 2 ≠ 0 := by positivity
  have h36 := not_dvd_pow hp hpq 36
  have h2m := not_dvd_pow_sub_one hord (show ¬ 4 ∣ 2 by norm_num)
  have h6 := not_dvd_pow_sub_one hord (show ¬ 4 ∣ 6 by norm_num)
  have h9 := not_dvd_pow_add_one hord (show ¬ 4 ∣ 2 * 9 by norm_num)
  have h5 := not_dvd_pow_add_one hord (show ¬ 4 ∣ 2 * 5 by norm_num)
  have h4' : ¬ (p : ℤ) ∣ (q : ℤ) ^ 4 + 1 := hnd _ (by push_cast; exact f2)
  have h8' : ¬ (p : ℤ) ∣ (q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1 := hnd _ (by push_cast; exact f3)
  refine ordProj_eq_of_int_cofactor hn₀
    (R := (q : ℤ) ^ 36 * (((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1)) *
      ((q : ℤ) ^ 9 + 1) * (((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 4 + 1)) * ((q : ℤ) ^ 6 - 1) *
      ((q : ℤ) ^ 5 + 1) * ((q : ℤ) ^ 2 - 1)) ?_ ?_
  · simp only [Nat.cast_mul, cast_pow_sub_one hq1, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    ring
  · exact hpz.not_dvd_mul (hpz.not_dvd_mul (hpz.not_dvd_mul (hpz.not_dvd_mul
      (hpz.not_dvd_mul (hpz.not_dvd_mul h36 (hpz.not_dvd_mul h2m h8')) h9)
      (hpz.not_dvd_mul h2m h4')) h6) h5) h2m

end CTTw

theorem e6TwFour_ordProj {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hq : 2 ≤ q)
    (h : (p : ℤ) ∣ (q : ℤ) ^ 2 + 1) :
    p ^ (q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
        (q ^ 2 - 1)).factorization p =
      p ^ ((((q : ℤ) ^ 3 - (-1 : ℤ) * (q : ℤ) ^ 2 + (q : ℤ) - (-1 : ℤ)).natAbs) ^ 2
        ).factorization p := by
  obtain ⟨hpq, hord, hx, hq1⟩ := e6Four_data hp hp3 h
  have : Fact p.Prime := ⟨hp⟩
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := CTE6.natCast_ne_zero_of_lt (by norm_num) (by omega)
  have hp1 : ¬ (p : ℤ) ∣ (q : ℤ) + 1 := by
    intro hd
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
    push_cast at h0
    exact h2 (by push_cast; linear_combination hx - ((q : ZMod p) - 1) * h0)
  have hn₀ : (q ^ 2 + 1) ^ 2 ≠ 0 := by positivity
  have hF : (((q : ℤ) ^ 3 - (-1 : ℤ) * (q : ℤ) ^ 2 + (q : ℤ) - (-1 : ℤ)).natAbs) =
      (q + 1) * (q ^ 2 + 1) := by
    have : ((q : ℤ) ^ 3 - (-1 : ℤ) * (q : ℤ) ^ 2 + (q : ℤ) - (-1 : ℤ)) =
        (((q + 1) * (q ^ 2 + 1) : ℕ) : ℤ) := by
      push_cast
      ring
    rw [this, Int.natAbs_natCast]
  rw [CTTw.ordProj_twisted_four hp hp3 hq hpq hord hx, hF]
  have hcof := CTTw.ordProj_eq_of_int_cofactor (p := p) (N := ((q + 1) * (q ^ 2 + 1)) ^ 2)
    (n := (q ^ 2 + 1) ^ 2) hn₀ (R := ((q : ℤ) + 1) ^ 2) (by push_cast; ring)
    (hpz.not_dvd_mul hp1 hp1 |> fun h => by simpa [sq] using h)
  rw [hcof]

end CFSG.RankThree.PartOne.KE
