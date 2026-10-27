
module

public import CFSG.RankThree.Native.LySeedOperatorBase

public import CFSG.RankThree.Native.LySeedCheck

public section

namespace CFSG.RankThree.Native

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native Matrix CFSG.LinearAlgebra
open CFSG.Sporadic.He.Native (toMat toMat_mulM toMat_powM toMat_idM toMat_eq_of_beq mulM powM
  idM invM)

theorem ly_seed_parts :
    lyCheckAB14 = true ∧ lyCheckAB7 = true ∧ lyCheckAB2 = true ∧ lyCheckA = true ∧
      lyCheckB = true ∧ lyCheckX = true ∧ lyCheckFsymm = true ∧ lyCheckFinv = true ∧
      lyCheckS = true ∧ lyCheckE = true := by
  have h := ly_seed_check
  simp only [lySeedChecks, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem mA_ne_one : mA ≠ 1 := by
  rw [← toMat_matA]
  exact toMat_ne_one_of_lyNeId (show lyNeId matA = true from ly_seed_parts.2.2.2.1)

theorem mB_ne_one : mB ≠ 1 := by
  rw [← toMat_matB]
  exact toMat_ne_one_of_lyNeId (show lyNeId matB = true from ly_seed_parts.2.2.2.2.1)

theorem mX_ne_one : mX ≠ 1 := by
  rw [← toMat_matX]
  exact toMat_ne_one_of_lyNeId (show lyNeId matX = true from ly_seed_parts.2.2.2.2.2.1)

theorem mAB_pow_14 : (mA * mB) ^ 14 = 1 := by
  have e := toMat_eq_of_beq (p := 5) (d := 111) (show (powM 5 111 lyAB 14 == idM 111) = true from
    ly_seed_parts.1)
  rwa [toMat_matAB, toMat_idM] at e

theorem orderOf_mA [CFSG.Sporadic.Ly.LySeed] : orderOf mA = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact mA_sq) mA_ne_one

theorem orderOf_mB [CFSG.Sporadic.Ly.LySeed] : orderOf mB = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime mB_pow mB_ne_one

theorem orderOf_mAB : orderOf (mA * mB) = 14 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) mAB_pow_14 fun p hp hpd => ?_
  have hp' : p = 2 ∨ p = 7 := by
    rcases (Nat.Prime.dvd_mul hp).1 (show p ∣ 2 * 7 by simpa using hpd) with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)
  rcases hp' with rfl | rfl
  · rw [show 14 / 2 = 7 by norm_num, ← toMat_matAB]
    exact toMat_ne_one_of_lyNeId (show lyNeId (powM 5 111 lyAB 7) = true from ly_seed_parts.2.1)
  · rw [show 14 / 7 = 2 by norm_num, ← toMat_matAB]
    exact toMat_ne_one_of_lyNeId
      (show lyNeId (powM 5 111 lyAB 2) = true from ly_seed_parts.2.2.1)

theorem orderOf_lyConj [CFSG.Sporadic.Ly.LySeed] : orderOf (mA * lyG⁻¹ * mB * lyG) = 67 := by
  have : Fact (Nat.Prime 67) := ⟨by norm_num⟩
  rw [lyConj_eq]
  exact orderOf_eq_prime mX_pow mX_ne_one

theorem lyF_symm : lyFᵀ = lyF := by
  have e := toMat_eq_of_beq (p := 5) (d := 111)
    (show (transM formF == formF) = true from ly_seed_parts.2.2.2.2.2.2.1)
  rw [toMat_transM] at e
  exact e

theorem lyF_mul_inv : lyF * toMat 5 111 (invM 5 111 formF) = 1 := by
  have e := toMat_eq_of_beq (p := 5) (d := 111)
    (show (mulM 5 111 formF (invM 5 111 formF) == idM 111) = true from
      ly_seed_parts.2.2.2.2.2.2.2.1)
  rwa [toMat_mulM, toMat_idM] at e

theorem isUnit_lyF : IsUnit lyF :=
  (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse lyF_mul_inv)

theorem lyF_det_ne_zero : lyF.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det lyF).1 isUnit_lyF).ne_zero

theorem lyS_symm : lySᵀ = lyS := by
  have h : lyCheckS = true := ly_seed_parts.2.2.2.2.2.2.2.2.1
  simp only [lyCheckS, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  ext a b
  rw [transpose_apply, lyS, ← mat7_keyS]
  simp only [mat7, of_apply]
  rw [h b.val b.isLt a.val a.isLt]

theorem lyE_sq : lyE ^ 2 = 0 := by
  have e := toMat_eq_of_beq (p := 5) (d := 111)
    (show (mulM 5 111 lyEArr lyEArr == lyZeroM) = true from ly_seed_parts.2.2.2.2.2.2.2.2.2)
  rw [toMat_mulM, toMat_lyEArr, toMat_lyZeroM] at e
  rw [sq, e]

theorem FAM_Ly_seed_and_operator_properties [CFSG.Sporadic.Ly.LySeed] :
    mA.det = 1 ∧ mB.det = 1 ∧ orderOf mA = 2 ∧ orderOf mB = 5 ∧ orderOf (mA * mB) = 14 ∧
      orderOf (mA * lyG⁻¹ * mB * lyG) = 67 ∧ lyFᵀ = lyF ∧ lyF.det ≠ 0 ∧ lySᵀ = lyS ∧
      lyE = lyU * lyS * lyUᵀ * lyF ∧ lyE ^ 2 = 0 :=
  ⟨det_mA, det_mB, orderOf_mA, orderOf_mB, orderOf_mAB, orderOf_lyConj, lyF_symm,
    lyF_det_ne_zero, lyS_symm, rfl, lyE_sq⟩

end CFSG.RankThree.Native
