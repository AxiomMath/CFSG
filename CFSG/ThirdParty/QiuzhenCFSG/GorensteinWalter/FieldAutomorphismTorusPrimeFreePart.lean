module

public import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Ring.Parity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Prime-free parts of field-automorphism tori

For an odd prime-order field automorphism, LTE bounds the `p`-part of
`r ^ p ± 1` by one more than the `p`-part of `r ± 1`.  Consequently,
divisibility of the complementary prime-free torus parts gives the exact
linear upper bound needed in the semilinear centralizer argument.
-/

namespace CFSG.GorensteinWalter

private theorem prime_dvd_pow_self_sub_nat
    (p r : ℕ) (hp : p.Prime) :
    p ∣ r ^ p - r := by
  have hrle : r ≤ r ^ p := Nat.le_pow hp.pos
  have h := Int.prime_dvd_pow_self_sub hp (r : ℤ)
  apply Int.natCast_dvd_natCast.mp
  simpa [Int.natCast_sub hrle] using h

private theorem padicVal_pow_sub_one_le
    (p r : ℕ) (hp : p.Prime) (hpodd : Odd p) (hr : 2 ≤ r) :
    padicValNat p (r ^ p - 1) ≤ padicValNat p (r - 1) + 1 := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hbase : p ∣ r - 1
  · have hpr : ¬ p ∣ r := by
      intro hpr
      have hd : p ∣ r - (r - 1) := Nat.dvd_sub hpr hbase
      have heq : r - (r - 1) = 1 := by omega
      have hpone : p ∣ 1 := heq ▸ hd
      exact hp.ne_one (Nat.dvd_one.mp hpone)
    have hv := padicValNat.pow_sub_pow hpodd (x := r) (y := 1)
      (by omega) hbase hpr hp.ne_zero
    simpa [padicValNat.self hp.one_lt] using hv.le
  · have hpow : ¬ p ∣ r ^ p - 1 := by
      intro h
      have hfermat : p ∣ r ^ p - r := prime_dvd_pow_self_sub_nat p r hp
      have hd : p ∣ (r ^ p - 1) - (r ^ p - r) := Nat.dvd_sub h hfermat
      have heq : (r ^ p - 1) - (r ^ p - r) = r - 1 := by
        have := Nat.le_pow hp.pos (a := r)
        omega
      exact hbase (heq ▸ hd)
    rw [padicValNat.eq_zero_of_not_dvd hpow]
    omega

private theorem padicVal_pow_add_one_le
    (p r : ℕ) (hp : p.Prime) (hpodd : Odd p) (hr : 1 ≤ r) :
    padicValNat p (r ^ p + 1) ≤ padicValNat p (r + 1) + 1 := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hbase : p ∣ r + 1
  · have hpr : ¬ p ∣ r := by
      intro hpr
      have hpone : p ∣ 1 := by
        simpa using Nat.dvd_sub hbase hpr
      exact hp.ne_one (Nat.dvd_one.mp hpone)
    have hv := padicValNat.pow_add_pow hpodd (x := r) (y := 1)
      hbase hpr hpodd
    simpa [padicValNat.self hp.one_lt] using hv.le
  · have hpow : ¬ p ∣ r ^ p + 1 := by
      intro h
      have hfermat : p ∣ r ^ p - r := prime_dvd_pow_self_sub_nat p r hp
      have hd : p ∣ (r ^ p + 1) - (r ^ p - r) := Nat.dvd_sub h hfermat
      have heq : (r ^ p + 1) - (r ^ p - r) = r + 1 := by
        have := Nat.le_pow hp.pos (a := r)
        omega
      exact hbase (heq ▸ hd)
    rw [padicValNat.eq_zero_of_not_dvd hpow]
    omega

private theorem le_prime_mul_of_divMaxPow_dvd
    (p n m : ℕ) (hp : p.Prime) (hm : 0 < m)
    (hval : padicValNat p n ≤ padicValNat p m + 1)
    (hdiv : n.divMaxPow p ∣ m.divMaxPow p) :
    n ≤ p * m := by
  have hpow : p ^ padicValNat p n ≤ p ^ (padicValNat p m + 1) :=
    Nat.pow_le_pow_right hp.pos hval
  have hm0pos : 0 < m.divMaxPow p := by
    have hmdecomp := Nat.pow_padicValNat_mul_divMaxPow p m
    by_contra h
    have hm0 : m.divMaxPow p = 0 := by omega
    rw [hm0, mul_zero] at hmdecomp
    omega
  have hpart : n.divMaxPow p ≤ m.divMaxPow p :=
    Nat.le_of_dvd hm0pos hdiv
  calc
    n = p ^ padicValNat p n * n.divMaxPow p :=
      (Nat.pow_padicValNat_mul_divMaxPow p n).symm
    _ ≤ p ^ (padicValNat p m + 1) * m.divMaxPow p :=
      Nat.mul_le_mul hpow hpart
    _ = p * (p ^ padicValNat p m * m.divMaxPow p) := by ring
    _ = p * m := by rw [Nat.pow_padicValNat_mul_divMaxPow]

/-- For `r ≥ 3` and an odd prime `p`, divisibility of the `p`-free part of
one of the two field-torus orders by the corresponding fixed-field part
forces the linear upper bound for that sign. -/
public theorem fieldAutomorphism_torus_primeFreePart_bounds
    (r p : ℕ) (hr : 3 ≤ r) (hp : p.Prime) (hpodd : Odd p) :
    (((r ^ p - 1).divMaxPow p ∣ (r - 1).divMaxPow p) →
      r ^ p - 1 ≤ p * (r - 1)) ∧
    (((r ^ p + 1).divMaxPow p ∣ (r + 1).divMaxPow p) →
      r ^ p + 1 ≤ p * (r + 1)) := by
  constructor
  · intro hdiv
    exact le_prime_mul_of_divMaxPow_dvd p (r ^ p - 1) (r - 1) hp
      (by omega) (padicVal_pow_sub_one_le p r hp hpodd (by omega)) hdiv
  · intro hdiv
    exact le_prime_mul_of_divMaxPow_dvd p (r ^ p + 1) (r + 1) hp
      (by omega) (padicVal_pow_add_one_le p r hp hpodd (by omega)) hdiv

end CFSG.GorensteinWalter
