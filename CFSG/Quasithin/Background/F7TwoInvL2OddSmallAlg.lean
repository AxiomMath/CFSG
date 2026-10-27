module

public import CFSG.Quasithin.Background.F7TwoInvAutWrap
public import CFSG.CharacterTheory.PSL2Table.Basic

public section

namespace CFSG.Quasithin.F7Two

open CFSG.PSL2Table
open scoped MatrixGroups Polynomial

theorem not_isPGroup_two_zpowers_of_pow_odd {G : Type*} [Group G] {g : G} {m : ℕ} (hm : Odd m)
    (h : g ^ m = 1) (h1 : g ≠ 1) : ¬ IsPGroup 2 ↥(Subgroup.zpowers g) := by
  rw [isPGroup_zpowers_iff]
  rintro ⟨k, hk⟩
  have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right k hm.coprime_two_right
  exact h1 (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h)
    (orderOf_dvd_of_pow_eq_one hk)))

theorem sl2_mul_self {K : Type} [Field K] (B : SL(2, K)) :
    (B : Matrix (Fin 2) (Fin 2) K) * (B : Matrix (Fin 2) (Fin 2) K) =
      ((B : Matrix (Fin 2) (Fin 2) K) 0 0 + (B : Matrix (Fin 2) (Fin 2) K) 1 1) •
        (B : Matrix (Fin 2) (Fin 2) K) - 1 := by
  have hdet := det_entries B
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (-1 : K) * hdet
  · ring
  · ring
  · linear_combination (-1 : K) * hdet

theorem pow_three_eq_one_of_mul_self {A : Type*} [Ring A] {B : A} (hCH : B * B = -B - 1) :
    B ^ 3 = 1 := by
  calc B ^ 3 = B * B * B := by noncomm_ring
    _ = (-B - 1) * B := by rw [hCH]
    _ = -(B * B) - B := by noncomm_ring
    _ = 1 := by rw [hCH]; noncomm_ring

theorem pow_four_eq_neg_one_of_mul_self {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {B : A}
    {t : R} (hCH : B * B = t • B - 1) (ht : t ^ 2 = 2) : B ^ 4 = -1 := by
  have h0 : Polynomial.aeval B ((Polynomial.X : R[X]) ^ 2 - Polynomial.C t * Polynomial.X + 1) =
      0 := by
    simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      map_one]
    rw [sq, hCH, ← Algebra.smul_def]
    abel
  have key : (Polynomial.X ^ 4 + 1 : R[X]) =
      (Polynomial.X ^ 2 + Polynomial.C t * Polynomial.X + 1) *
        (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1) := by
    have ht' : (Polynomial.C t) ^ 2 = 2 := by
      rw [← Polynomial.C_pow, ht]
      exact map_ofNat Polynomial.C 2
    linear_combination Polynomial.X ^ 2 * ht'
  have h1 := congrArg (Polynomial.aeval B) key
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, map_one, h0, mul_zero] at h1
  exact eq_neg_of_add_eq_zero_left h1

theorem pow_five_eq_neg_one_of_mul_self {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {B : A}
    {t : R} (hCH : B * B = t • B - 1) (ht : t ^ 2 = t + 1) : B ^ 5 = -1 := by
  have h0 : Polynomial.aeval B ((Polynomial.X : R[X]) ^ 2 - Polynomial.C t * Polynomial.X + 1) =
      0 := by
    simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      map_one]
    rw [sq, hCH, ← Algebra.smul_def]
    abel
  have key : (Polynomial.X ^ 5 + 1 : R[X]) = (Polynomial.X + 1) *
      (Polynomial.X ^ 2 + Polynomial.C (t - 1) * Polynomial.X + 1) *
        (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1) := by
    have ht' : (Polynomial.C t) ^ 2 = Polynomial.C t + 1 := by
      rw [← Polynomial.C_pow, ht, Polynomial.C_add, Polynomial.C_1]
    rw [Polynomial.C_sub, Polynomial.C_1]
    linear_combination (Polynomial.X + 1) * Polynomial.X ^ 2 * ht'
  have h1 := congrArg (Polynomial.aeval B) key
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, map_one, h0, mul_zero] at h1
  exact eq_neg_of_add_eq_zero_left h1

theorem mk_mem_invXiAut_of_pow_odd {K : Type} [Field K] {φ : MulAut (PSL(2, K))} {A A' : SL(2, K)}
    (hφ : φ (mk A) = mk A') {m : ℕ} (hm : Odd m)
    (hBm : (A' * A⁻¹) ^ m = 1 ∨ (A' * A⁻¹) ^ m = -1) (hB1 : A' * A⁻¹ ≠ 1)
    (hB2 : A' * A⁻¹ ≠ -1) : mk A ∈ invXiAut φ := by
  show ¬ IsPGroup 2 ↥(Subgroup.zpowers (φ (mk A) * (mk A)⁻¹))
  have e : φ (mk A) * (mk A)⁻¹ = mk (A' * A⁻¹) := by rw [hφ, map_mul, map_inv]
  rw [e]
  refine not_isPGroup_two_zpowers_of_pow_odd hm ?_ ?_
  · rw [← map_pow]
    exact (mk_eq_one_iff _).2 hBm
  · rw [Ne, mk_eq_one_iff, not_or]
    exact ⟨hB1, hB2⟩

end CFSG.Quasithin.F7Two
