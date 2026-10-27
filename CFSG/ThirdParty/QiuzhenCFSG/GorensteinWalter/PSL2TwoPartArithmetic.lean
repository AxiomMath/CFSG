module

public import Mathlib.Data.Nat.Factorization.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Two-part arithmetic for the odd `PSL₂` order formula
-/

namespace CFSG.GorensteinWalter

open Nat

public theorem psl2_order_two_factorization_split {q : ℕ} (hq : Odd q) (hq1 : 1 < q)
    (heven : Even ((q - 1) / 2)) :
    (q * (q ^ 2 - 1) / 2).factorization 2 =
      ((q - 1) / 2).factorization 2 + 1 := by
  have hq0 : q ≠ 0 := by omega
  have hqm1 : q - 1 ≠ 0 := by omega
  have hqp1 : q + 1 ≠ 0 := by omega
  have h2qm1 : 2 ∣ q - 1 := by
    rcases hq with ⟨k, hk⟩
    use k
    omega
  have h2qp1 : 2 ∣ q + 1 := by
    rcases hq with ⟨k, hk⟩
    use k + 1
    omega
  have hfactor : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    simpa using (Nat.sq_sub_sq q 1)
  have hqfac : q.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      rcases hq with ⟨k, hk⟩
      intro h
      rcases h with ⟨l, hl⟩
      omega)
  have h2fac : (2 : ℕ).factorization 2 = 1 :=
    Nat.Prime.factorization_self Nat.prime_two
  have hfacm1 : (q - 1).factorization 2 =
      ((q - 1) / 2).factorization 2 + 1 := by
    have hmul : 2 * ((q - 1) / 2) = q - 1 := Nat.mul_div_cancel' h2qm1
    have hmulFac : (2 * ((q - 1) / 2)).factorization =
        (2 : ℕ).factorization + ((q - 1) / 2).factorization :=
      Nat.factorization_mul (a := 2) (b := (q - 1) / 2)
        (by omega) (by omega)
    calc
      (q - 1).factorization 2 = (2 * ((q - 1) / 2)).factorization 2 := by rw [hmul]
      _ = (2).factorization 2 + ((q - 1) / 2).factorization 2 := by
        simpa only [Finsupp.add_apply] using
          congrArg (fun f : Finsupp ℕ ℕ => f 2) hmulFac
      _ = ((q - 1) / 2).factorization 2 + 1 := by omega
  have hoddhalf : Odd ((q + 1) / 2) := by
    rcases hq with ⟨k, hk⟩
    rcases heven with ⟨l, hl⟩
    have hmulplus : 2 * ((q + 1) / 2) = q + 1 := Nat.mul_div_cancel' h2qp1
    use l
    omega
  have hfacp1 : (q + 1).factorization 2 = 1 := by
    have hmul : 2 * ((q + 1) / 2) = q + 1 := Nat.mul_div_cancel' h2qp1
    have hmulFac : (2 * ((q + 1) / 2)).factorization =
        (2 : ℕ).factorization + ((q + 1) / 2).factorization :=
      Nat.factorization_mul (a := 2) (b := (q + 1) / 2)
        (by omega) (by omega)
    have hhalfFac : ((q + 1) / 2).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h =>
        (not_even_iff_odd.mpr hoddhalf) (even_iff_two_dvd.mpr h))
    calc
      (q + 1).factorization 2 = (2 * ((q + 1) / 2)).factorization 2 := by rw [hmul]
      _ = (2).factorization 2 + ((q + 1) / 2).factorization 2 := by
        simpa only [Finsupp.add_apply] using
          congrArg (fun f : Finsupp ℕ ℕ => f 2) hmulFac
      _ = 1 := by omega
  have hdiv : 2 ∣ q * ((q + 1) * (q - 1)) := by
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h2qm1 (q + 1)) q
  rw [hfactor, Nat.factorization_div (n := q * ((q + 1) * (q - 1))) hdiv,
    Nat.factorization_mul hq0 (Nat.mul_ne_zero hqp1 hqm1),
    Nat.factorization_mul hqp1 hqm1]
  change q.factorization 2 + ((q + 1).factorization 2 + (q - 1).factorization 2) -
      (2 : ℕ).factorization 2 = ((q - 1) / 2).factorization 2 + 1
  rw [hqfac, hfacp1, hfacm1, h2fac]
  omega


public theorem psl2_order_two_factorization_nonsplit {q : ℕ} (hq : Odd q) (hq1 : 1 < q)
    (hodd : Odd ((q - 1) / 2)) :
    (q * (q ^ 2 - 1) / 2).factorization 2 =
      ((q + 1) / 2).factorization 2 + 1 := by
  have hq0 : q ≠ 0 := by omega
  have hqm1 : q - 1 ≠ 0 := by omega
  have hqp1 : q + 1 ≠ 0 := by omega
  have h2qm1 : 2 ∣ q - 1 := by
    rcases hq with ⟨k, hk⟩
    use k
    omega
  have h2qp1 : 2 ∣ q + 1 := by
    rcases hq with ⟨k, hk⟩
    use k + 1
    omega
  have hfactor : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    simpa using (Nat.sq_sub_sq q 1)
  have hqfac : q.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      rcases hq with ⟨k, hk⟩
      intro h
      rcases h with ⟨l, hl⟩
      omega)
  have h2fac : (2 : ℕ).factorization 2 = 1 :=
    Nat.Prime.factorization_self Nat.prime_two
  have hmulm : 2 * ((q - 1) / 2) = q - 1 := Nat.mul_div_cancel' h2qm1
  have hmulp : 2 * ((q + 1) / 2) = q + 1 := Nat.mul_div_cancel' h2qp1
  have hevenhalf : Even ((q + 1) / 2) := by
    rcases hodd with ⟨l, hl⟩
    use l + 1
    omega
  have hfacm1 : (q - 1).factorization 2 = 1 := by
    have hmulFac : (2 * ((q - 1) / 2)).factorization =
        (2 : ℕ).factorization + ((q - 1) / 2).factorization :=
      Nat.factorization_mul (a := 2) (b := (q - 1) / 2)
        (by omega) (by omega)
    have hhalfFac : ((q - 1) / 2).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h =>
        (not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h))
    calc
      (q - 1).factorization 2 = (2 * ((q - 1) / 2)).factorization 2 := by rw [hmulm]
      _ = (2).factorization 2 + ((q - 1) / 2).factorization 2 := by
        simpa only [Finsupp.add_apply] using
          congrArg (fun f : Finsupp ℕ ℕ => f 2) hmulFac
      _ = 1 := by omega
  have hfacp1 : (q + 1).factorization 2 =
      ((q + 1) / 2).factorization 2 + 1 := by
    have hmulFac : (2 * ((q + 1) / 2)).factorization =
        (2 : ℕ).factorization + ((q + 1) / 2).factorization :=
      Nat.factorization_mul (a := 2) (b := (q + 1) / 2)
        (by omega) (by omega)
    calc
      (q + 1).factorization 2 = (2 * ((q + 1) / 2)).factorization 2 := by rw [hmulp]
      _ = (2).factorization 2 + ((q + 1) / 2).factorization 2 := by
        simpa only [Finsupp.add_apply] using
          congrArg (fun f : Finsupp ℕ ℕ => f 2) hmulFac
      _ = ((q + 1) / 2).factorization 2 + 1 := by omega
  have hdiv : 2 ∣ q * ((q + 1) * (q - 1)) := by
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h2qm1 (q + 1)) q
  rw [hfactor, Nat.factorization_div (n := q * ((q + 1) * (q - 1))) hdiv,
    Nat.factorization_mul hq0 (Nat.mul_ne_zero hqp1 hqm1),
    Nat.factorization_mul hqp1 hqm1]
  change q.factorization 2 + ((q + 1).factorization 2 + (q - 1).factorization 2) -
      (2 : ℕ).factorization 2 = ((q + 1) / 2).factorization 2 + 1
  rw [hqfac, hfacp1, hfacm1, h2fac]
  omega

end CFSG.GorensteinWalter
