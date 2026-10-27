module

public import CFSG.RankThree.PartTwo.Sec16.KL3SubProofElat

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace KL3SubProof

open Matrix

variable {K : Type} [Field K]

@[expose] def utm (a b c : K) : Matrix (Fin 3) (Fin 3) K := !![1, a, c; 0, 1, b; 0, 0, 1]

@[expose] def IsUT (M : Matrix (Fin 3) (Fin 3) K) : Prop :=
  M 0 0 = 1 ∧ M 1 1 = 1 ∧ M 2 2 = 1 ∧ M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0

theorem IsUT.eq_utm {M : Matrix (Fin 3) (Fin 3) K} (h : IsUT M) :
    M = utm (M 0 1) (M 1 2) (M 0 2) := by
  obtain ⟨h00, h11, h22, h10, h20, h21⟩ := h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [utm, h00, h11, h22, h10, h20, h21]

theorem isUT_utm (a b c : K) : IsUT (utm a b c) := by
  simp [IsUT, utm]

@[simp] theorem utm_apply_zero_one (a b c : K) : utm a b c 0 1 = a := by simp [utm]

@[simp] theorem utm_apply_one_two (a b c : K) : utm a b c 1 2 = b := by simp [utm]

@[simp] theorem utm_apply_zero_two (a b c : K) : utm a b c 0 2 = c := by simp [utm]

theorem utm_mul (a b c a' b' c' : K) :
    utm a b c * utm a' b' c' = utm (a + a') (b + b') (c + a * b' + c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [utm, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem utm_inj {a b c a' b' c' : K} (h : utm a b c = utm a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h1 := congrFun (congrFun h 0) 1
  have h2 := congrFun (congrFun h 1) 2
  have h3 := congrFun (congrFun h 0) 2
  simp only [utm_apply_zero_one, utm_apply_one_two, utm_apply_zero_two] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem utm_zero : utm (0 : K) 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [utm]

theorem utm_eq_one_iff {a b c : K} : utm a b c = 1 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    rw [← utm_zero] at h
    exact utm_inj h
  · rintro ⟨rfl, rfl, rfl⟩
    exact utm_zero

section CharTwo

variable [CharP K 2]

theorem utm_mul_inv (a b c : K) : utm a b c * utm a b (c + a * b) = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [utm_mul, utm_eq_one_iff]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination a * h2
  · linear_combination b * h2
  · linear_combination (c + a * b) * h2

theorem utm_mul_self (a b c : K) : utm a b c * utm a b c = utm 0 0 (a * b) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [utm_mul]
  have e1 : a + a = 0 := by linear_combination a * h2
  have e2 : b + b = 0 := by linear_combination b * h2
  have e3 : c + a * b + c = a * b := by linear_combination c * h2
  rw [e1, e2, e3]

theorem utm_zero_zero_mul_self (c : K) : utm 0 0 c * utm 0 0 c = 1 := by
  rw [utm_mul_self, mul_zero, utm_zero]

theorem IsUT.coe_inv {g : GL (Fin 3) K} (h : IsUT (g : Matrix (Fin 3) (Fin 3) K)) :
    ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      utm ((g : Matrix (Fin 3) (Fin 3) K) 0 1) ((g : Matrix (Fin 3) (Fin 3) K) 1 2)
        ((g : Matrix (Fin 3) (Fin 3) K) 0 2 +
          (g : Matrix (Fin 3) (Fin 3) K) 0 1 * (g : Matrix (Fin 3) (Fin 3) K) 1 2) := by
  rw [Matrix.coe_units_inv]
  apply Matrix.inv_eq_right_inv
  conv_lhs => rw [h.eq_utm]
  exact utm_mul_inv _ _ _

@[expose] def utSub (K : Type) [Field K] [CharP K 2] : Subgroup (GL (Fin 3) K) where
  carrier := {g | IsUT (g : Matrix (Fin 3) (Fin 3) K)}
  mul_mem' := by
    intro g h hg hh
    change IsUT ((g * h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    have hg' : IsUT (g : Matrix (Fin 3) (Fin 3) K) := hg
    have hh' : IsUT (h : Matrix (Fin 3) (Fin 3) K) := hh
    rw [Units.val_mul, hg'.eq_utm, hh'.eq_utm, utm_mul]
    exact isUT_utm _ _ _
  one_mem' := by
    change IsUT ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [Units.val_one, ← utm_zero]
    exact isUT_utm _ _ _
  inv_mem' := by
    intro g hg
    change IsUT ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [IsUT.coe_inv hg]
    exact isUT_utm _ _ _

theorem mem_utSub {g : GL (Fin 3) K} : g ∈ utSub K ↔ IsUT (g : Matrix (Fin 3) (Fin 3) K) :=
  Iff.rfl

theorem pow_four_eq_one_of_mem_utSub {g : GL (Fin 3) K} (hg : g ∈ utSub K) : g ^ 4 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, mem_utSub.mp hg |>.eq_utm,
    show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, utm_mul_self, utm_zero_zero_mul_self]

end CharTwo

@[expose] def colSub (K : Type) [Field K] : Subgroup (GL (Fin 3) K) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨?_, ?_⟩ <;>
      simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, hg1, hg2, hh1, hh2]
  one_mem' := by
    refine ⟨?_, ?_⟩ <;> simp
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    set v : Fin 3 → K := Pi.single 0 1 with hv
    have hgv : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = (g : Matrix (Fin 3) (Fin 3) K) 0 0 • v := by
      rw [hv, mulVec_single_one]
      ext i
      fin_cases i <;> simp [hg1, hg2]
    have hback : v = (g : Matrix (Fin 3) (Fin 3) K) 0 0 •
        (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by
      rw [← Matrix.mulVec_smul, ← hgv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mulVec]
    rw [hv, mulVec_single_one] at hback
    have e0 := congrFun hback 0
    have e1 := congrFun hback 1
    have e2 := congrFun hback 2
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.col_apply, Pi.single_eq_same] at e0
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at e1 e2
    rw [Pi.single_eq_of_ne (by decide)] at e1 e2
    have hg00 : (g : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at e0
      exact one_ne_zero e0
    exact ⟨(mul_eq_zero.mp e1.symm).resolve_left hg00, (mul_eq_zero.mp e2.symm).resolve_left hg00⟩

@[expose] def rowSub (K : Type) [Field K] : Subgroup (GL (Fin 3) K) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨?_, ?_⟩ <;>
      simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, hg1, hg2, hh1, hh2]
  one_mem' := by
    refine ⟨?_, ?_⟩ <;> simp
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    set v : Fin 3 → K := Pi.single 2 1 with hv
    have hgv : v ᵥ* (g : Matrix (Fin 3) (Fin 3) K) = (g : Matrix (Fin 3) (Fin 3) K) 2 2 • v := by
      rw [hv, single_one_vecMul]
      ext i
      fin_cases i <;> simp [hg1, hg2]
    have hback : v = (g : Matrix (Fin 3) (Fin 3) K) 2 2 •
        (v ᵥ* ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
      rw [← Matrix.smul_vecMul, ← hgv, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.vecMul_one]
    rw [hv, single_one_vecMul] at hback
    have e0 := congrFun hback 0
    have e1 := congrFun hback 1
    have e2 := congrFun hback 2
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.row_apply, Pi.single_eq_same] at e2
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.row_apply] at e0 e1
    rw [Pi.single_eq_of_ne (by decide)] at e0 e1
    have hg22 : (g : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at e2
      exact one_ne_zero e2
    exact ⟨(mul_eq_zero.mp e0.symm).resolve_left hg22, (mul_eq_zero.mp e1.symm).resolve_left hg22⟩

end KL3SubProof

end CFSG.RankThree.PartTwo.Sec16
