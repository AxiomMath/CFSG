module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148BHessOrth
public import CFSG.RankThree.PartTwo.Sec4.Ronan148BHessTrace
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148B

open Matrix CFSG.RankThree.SubgroupLists
open scoped commutatorElement

@[expose] def hessQ : Matrix (Fin 3) (Fin 3) ℤ := !![-7, -4, -4; 4, 1, -8; 4, -8, 1]

@[expose] def hessY : Matrix (Fin 3) (Fin 3) ℤ := !![-7, 4, -4; -4, 1, 8; 4, 8, 1]

theorem hessQ_pow_one : (hessQ ^ 1) 0 0 = -7 := by decide
theorem hessQ_pow_two : (hessQ ^ 2) 0 0 = 17 := by decide
theorem hessQ_pow_three : (hessQ ^ 3) 0 0 = 329 := by decide
theorem hessQ_pow_four : (hessQ ^ 4) 0 0 = -5983 := by decide
theorem hessQ_pow_five : (hessQ ^ 5) 0 0 = 57113 := by decide

theorem hessQY_comm : (hessQ * hessY - hessY * hessQ) 0 1 = -128 := by decide

theorem hessYQt_trace : (hessY * hessQᵀ).trace = -77 := by decide

section Field

variable {K : Type*} [Field K]

@[expose] def hessRho2 (h3 : (3 : K) ≠ 0) : GL (Fin 3) K := ⁅(hessT 0 : GL (Fin 3) K), hessS0 h3⁆

@[expose] def hessRho2y (h3 : (3 : K) ≠ 0) : GL (Fin 3) K :=
  (hessT 1 : GL (Fin 3) K) * hessRho2 h3 * hessT 1

theorem coe_hessRho2 (h3 : (3 : K) ≠ 0) :
    ((hessRho2 h3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (9 : K)⁻¹ • hessQ.map (Int.cast : ℤ → K) := by
  rw [hessRho2, commutatorElement_def]
  simp only [Units.val_mul, coe_hessT, coe_hessT_inv, coe_hessS0]
  rw [show (((hessS0 h3 : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    hessS0Mat from rfl]
  have h9 : (9 : K) ≠ 0 := by
    have : (9 : K) = 3 * 3 := by norm_num
    rw [this]
    exact mul_ne_zero h3 h3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hessTMat, hessS0Mat, Matrix.diagonal, hessQ] <;>
    field_simp <;>
    norm_num

theorem coe_hessRho2y (h3 : (3 : K) ≠ 0) :
    ((hessRho2y h3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (9 : K)⁻¹ • hessY.map (Int.cast : ℤ → K) := by
  rw [hessRho2y, Units.val_mul, Units.val_mul, coe_hessRho2, coe_hessT]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hessTMat, Matrix.diagonal, hessQ, hessY]

theorem hessRho2_mem_omegaGL (h3 : (3 : K) ≠ 0) :
    hessRho2 h3 ∈ omegaGL (1 : Matrix (Fin 3) (Fin 3) K) :=
  Subgroup.commutator_mem_commutator (hessT_mem_soGL 0) (hessS0_mem_soGL h3)

theorem hessRho2_mem_soGL (h3 : (3 : K) ≠ 0) :
    hessRho2 h3 ∈ soGL (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [hessRho2, commutatorElement_def]
  have h0 := hessT_mem_soGL (K := K) 0
  have hs := hessS0_mem_soGL h3
  exact mul_mem (mul_mem (mul_mem h0 hs) (inv_mem h0)) (inv_mem hs)

theorem coe_hessRho2_pow (h3 : (3 : K) ≠ 0) (k : ℕ) :
    (((hessRho2 h3) ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (9 : K)⁻¹ ^ k • (hessQ ^ k).map (Int.cast : ℤ → K) := by
  rw [Units.val_pow_eq_pow_val, coe_hessRho2, smul_pow]
  congr 1
  exact (map_pow (Int.castRingHom K).mapMatrix hessQ k).symm

theorem hessRho2y_eq (h3 : (3 : K) ≠ 0) :
    hessRho2y h3 = (hessT 1 : GL (Fin 3) K) * hessRho2 h3 * (hessT 1)⁻¹ := by
  apply Units.ext
  rfl

theorem coe_hessRho2_inv (h3 : (3 : K) ≠ 0) :
    (((hessRho2 h3)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (9 : K)⁻¹ • hessQᵀ.map (Int.cast : ℤ → K) := by
  have hso := (mem_soGL.mp (hessRho2_mem_soGL h3)).1
  rw [Matrix.mul_one] at hso
  have h1 : (((hessRho2 h3)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((hessRho2 h3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ := by
    calc (((hessRho2 h3)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        = ((hessRho2 h3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *
            ((hessRho2 h3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            (((hessRho2 h3)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [hso, Matrix.one_mul]
      _ = ((hessRho2 h3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ := by
          rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  rw [h1, coe_hessRho2, Matrix.transpose_smul, Matrix.transpose_map]

end Field

section CharP

variable {K : Type*} [Field K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]

theorem eq_of_dvd_pow_mul_pow {a b i j : ℕ} (ha : a.Prime) (hb : b.Prime)
    (h : p ∣ a ^ i * b ^ j) : p = a ∨ p = b := by
  rcases (Nat.Prime.dvd_mul hp.out).mp h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp.out ha).mp (hp.out.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp.out hb).mp (hp.out.dvd_of_dvd_pow h))

theorem natCast_ne_zero_of {n : ℕ} (h : ¬ p ∣ n) : (n : K) ≠ 0 := by
  intro h0
  exact h ((CharP.cast_eq_zero_iff K p n).mp h0)

theorem three_ne_zero_of (hp3 : p ≠ 3) : (3 : K) ≠ 0 := by
  have : ((3 : ℕ) : K) ≠ 0 := natCast_ne_zero_of (fun h =>
    hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp h))
  exact_mod_cast this

theorem two_ne_zero_of (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  have : ((2 : ℕ) : K) ≠ 0 := natCast_ne_zero_of (fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h))
  exact_mod_cast this

theorem nine_pow_eq_of_hessRho2_pow (h3 : (3 : K) ≠ 0) {k : ℕ} (hk : (hessRho2 h3) ^ k = 1) :
    ((9 ^ k - (hessQ ^ k) 0 0 : ℤ) : K) = 0 := by
  have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hk
  simp only [coe_hessRho2_pow, Units.val_one, Matrix.smul_apply, Matrix.map_apply,
    Matrix.one_apply_eq, smul_eq_mul] at h
  have h9 : (9 : K) ≠ 0 := by
    have : (9 : K) = 3 * 3 := by norm_num
    rw [this]
    exact mul_ne_zero h3 h3
  have h' : (((hessQ ^ k) 0 0 : ℤ) : K) = 9 ^ k := by
    rw [← mul_one ((9 : K) ^ k), ← h, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ h9, one_pow,
      one_mul]
  push_cast
  rw [h', sub_self]

theorem hessRho2_pow_ne_one (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7)
    (hp11 : p ≠ 11) {k : ℕ} (hk1 : 1 ≤ k) (hk5 : k ≤ 5) :
    (hessRho2 (three_ne_zero_of (K := K) hp3)) ^ k ≠ 1 := by
  intro hk
  have h := nine_pow_eq_of_hessRho2_pow _ hk
  have hdvd := (CharP.intCast_eq_zero_iff K p _).mp h
  have key : ∀ n : ℕ, (p : ℤ) ∣ (n : ℤ) → p ∣ n := fun n h => Int.natCast_dvd_natCast.mp h
  interval_cases k
  · rw [hessQ_pow_one] at hdvd
    have : p ∣ 2 ^ 4 * 3 ^ 0 := key _ (by norm_num at hdvd ⊢; exact hdvd)
    rcases eq_of_dvd_pow_mul_pow Nat.prime_two Nat.prime_three this with h | h <;> omega
  · rw [hessQ_pow_two] at hdvd
    have : p ∣ 2 ^ 6 * 3 ^ 0 := key _ (by norm_num at hdvd ⊢; exact hdvd)
    rcases eq_of_dvd_pow_mul_pow Nat.prime_two Nat.prime_three this with h | h <;> omega
  · rw [hessQ_pow_three] at hdvd
    have : p ∣ 2 ^ 4 * 5 ^ 2 := key _ (by norm_num at hdvd ⊢; exact hdvd)
    rcases eq_of_dvd_pow_mul_pow Nat.prime_two Nat.prime_five this with h | h <;> omega
  · rw [hessQ_pow_four] at hdvd
    have : p ∣ 2 ^ 8 * 7 ^ 2 := key _ (by norm_num at hdvd ⊢; exact hdvd)
    rcases eq_of_dvd_pow_mul_pow Nat.prime_two (by norm_num) this with h | h <;> omega
  · rw [hessQ_pow_five] at hdvd
    have : p ∣ 2 ^ 4 * 11 ^ 2 := key _ (by norm_num at hdvd ⊢; exact hdvd)
    rcases eq_of_dvd_pow_mul_pow Nat.prime_two (by norm_num) this with h | h <;> omega

theorem hessRho2_mul_ne (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    hessRho2 (three_ne_zero_of (K := K) hp3) * hessRho2y (three_ne_zero_of hp3) ≠
      hessRho2y (three_ne_zero_of hp3) * hessRho2 (three_ne_zero_of hp3) := by
  intro h
  have h3 := three_ne_zero_of (K := K) hp3
  have h9 : (9 : K) ≠ 0 := by
    have : (9 : K) = 3 * 3 := by norm_num
    rw [this]
    exact mul_ne_zero h3 h3
  have h' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 1) h
  simp only [Units.val_mul, coe_hessRho2, coe_hessRho2y] at h'
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul] at h'
  have e : (Int.cast : ℤ → K) = ⇑(Int.castRingHom K) := rfl
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul] at h'
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h'
  have h'' : (((hessQ * hessY - hessY * hessQ) 0 1 : ℤ) : K) = 0 := by
    rw [Matrix.sub_apply, Int.cast_sub]
    have := mul_left_cancel₀ (inv_ne_zero h9) (mul_left_cancel₀ (inv_ne_zero h9) h')
    change (Int.castRingHom K) ((hessQ * hessY) 0 1) - (Int.castRingHom K) ((hessY * hessQ) 0 1) = 0
    rw [this, sub_self]
  rw [hessQY_comm] at h''
  have hdvd := (CharP.intCast_eq_zero_iff K p _).mp h''
  have : p ∣ 2 ^ 7 * 3 ^ 0 := Int.natCast_dvd_natCast.mp (by norm_num at hdvd ⊢; exact hdvd)
  rcases eq_of_dvd_pow_mul_pow Nat.prime_two Nat.prime_three this with h | h <;> omega

theorem hessRho2Comm_pow_ne_one (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    ((hessT 1 : GL (Fin 3) K) * hessRho2 (three_ne_zero_of hp3) * (hessT 1)⁻¹ *
      (hessRho2 (three_ne_zero_of hp3))⁻¹) ^ p ≠ 1 := by
  intro h
  have h3 := three_ne_zero_of (K := K) hp3
  have h9 : (9 : K) ≠ 0 := by
    have : (9 : K) = 3 * 3 := by norm_num
    rw [this]
    exact mul_ne_zero h3 h3
  have hm := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h
  simp only [Units.val_pow_eq_pow_val, Units.val_one] at hm
  have htr := trace_eq_of_pow_char_eq_one (p := p) hm
  have e : (Int.cast : ℤ → K) = ⇑(Int.castRingHom K) := rfl
  rw [← hessRho2y_eq, Units.val_mul, coe_hessRho2y, coe_hessRho2_inv, Matrix.smul_mul,
    Matrix.mul_smul, e, ← Matrix.map_mul, Matrix.trace_smul, Matrix.trace_smul] at htr
  rw [← AddMonoidHom.map_trace (Int.castRingHom K), hessYQt_trace] at htr
  simp only [smul_eq_mul, map_neg, eq_intCast, Int.cast_ofNat] at htr
  have h320 : ((320 : ℕ) : K) = 0 := by
    field_simp at htr
    push_cast
    linear_combination -htr
  have hdvd := (CharP.cast_eq_zero_iff K p _).mp h320
  have : p ∣ 2 ^ 6 * 5 ^ 1 := by norm_num; exact hdvd
  rcases eq_of_dvd_pow_mul_pow Nat.prime_two Nat.prime_five this with h | h <;> omega

end CharP

end CFSG.RankThree.PartTwo.Sec4.Ronan148B
