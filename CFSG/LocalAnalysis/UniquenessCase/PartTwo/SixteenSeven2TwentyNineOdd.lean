module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s16c167_odd_centralizes {H : Type} [Group H] {O Z : Subgroup H} (hZO : Z ≤ O)
    (hZodd : Odd (Nat.card ↥Z)) (hZn : ∀ y ∈ O, ∀ z ∈ Z, y * z * y⁻¹ ∈ Z)
    (hC : ∀ y ∈ O, (∀ z ∈ Z, y * z = z * y) → y ∈ Z) {x : H} {k : ℕ} (hx : x ^ (2 ^ k) = 1)
    (hxO : ∀ y ∈ O, x * y * x⁻¹ ∈ O) (hxZ : ∀ z ∈ Z, x * z = z * x) :
    ∀ y ∈ O, x * y = y * x := by
  have hxZconj : ∀ z ∈ Z, x * z * x⁻¹ = z := by
    intro z hz
    rw [hxZ z hz]
    group
  have hxZinv : ∀ z ∈ Z, x⁻¹ * z * x = z := by
    intro z hz
    calc x⁻¹ * z * x = x⁻¹ * (z * x) := by rw [mul_assoc]
      _ = x⁻¹ * (x * z) := by rw [← hxZ z hz]
      _ = z := by group
  intro y hyO
  set y' : H := x * y * x⁻¹ with hy'def
  have hy'O : y' ∈ O := hxO y hyO
  set w : H := y⁻¹ * y' with hwdef
  have hwO : w ∈ O := O.mul_mem (O.inv_mem hyO) hy'O
  have hwZ : w ∈ Z := by
    apply hC w hwO
    intro z hz
    have hy'conj : y' * z * y'⁻¹ = y * z * y⁻¹ := by
      calc y' * z * y'⁻¹ = x * y * (x⁻¹ * z * x) * y⁻¹ * x⁻¹ := by rw [hy'def]; group
        _ = x * y * z * y⁻¹ * x⁻¹ := by rw [hxZinv z hz]
        _ = x * (y * z * y⁻¹) * x⁻¹ := by group
        _ = y * z * y⁻¹ := hxZconj _ (hZn y hyO z hz)
    have hconj : w * z * w⁻¹ = z := by
      calc w * z * w⁻¹ = y⁻¹ * (y' * z * y'⁻¹) * y := by rw [hwdef]; group
        _ = y⁻¹ * (y * z * y⁻¹) * y := by rw [hy'conj]
        _ = z := by group
    exact mul_inv_eq_iff_eq_mul.mp hconj
  have hxw : x * y * x⁻¹ = y * w := by
    rw [hwdef, hy'def]; group
  have hiter : ∀ n : ℕ, x ^ n * y * (x ^ n)⁻¹ = y * w ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc x ^ (n + 1) * y * (x ^ (n + 1))⁻¹
            = x * (x ^ n * y * (x ^ n)⁻¹) * x⁻¹ := by rw [pow_succ']; group
          _ = x * (y * w ^ n) * x⁻¹ := by rw [ih]
          _ = (x * y * x⁻¹) * (x * w ^ n * x⁻¹) := by group
          _ = (y * w) * w ^ n := by rw [hxw, hxZconj (w ^ n) (pow_mem hwZ n)]
          _ = y * w ^ (n + 1) := by rw [pow_succ']; group
  have hwpow : w ^ (2 ^ k) = 1 := by
    have h := hiter (2 ^ k)
    rw [hx] at h
    have h' : y * 1 = y * w ^ (2 ^ k) := by simpa using h
    exact (mul_left_cancel h').symm
  have hcop : Nat.Coprime (Nat.card ↥Z) (2 ^ k) :=
    (Nat.coprime_two_right.mpr hZodd).pow_right k
  have horder : orderOf w = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (Z.orderOf_dvd_natCard hwZ)
      (orderOf_dvd_iff_pow_eq_one.mpr hwpow)
  have hw1 : w = 1 := orderOf_eq_one_iff.mp horder
  have hxy : x * y * x⁻¹ = y := by rw [hxw, hw1, mul_one]
  exact mul_inv_eq_iff_eq_mul.mp hxy

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
