module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K]

theorem dvd_orderOf_mk_of_forall_scalar (h : UnitaryFieldData 2 f K)
    (y : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) {N : ℕ}
    (hN : ∀ (k : ℕ) (c : Kˣ), ((y : GL (Fin 3) K)) ^ k = GeneralLinearGroup.scalar (Fin 3) c →
      N ∣ k) :
    N ∣ orderOf (y : primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  have h1 := pow_orderOf_eq_one
    (y : primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  obtain ⟨c, -, -, hc⟩ := h1
  exact hN _ c (by rw [← hc, Subgroup.coe_pow])

theorem fieldAut_mk_mul_inv (h : UnitaryFieldData 2 f K)
    (hC : IsPrimeFormGram (1 : GL (Fin 3) K)) (φ : K ≃+* K)
    (y : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    primeFormFieldAut h hC φ (y : primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
        (y : primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))⁻¹ =
      ((primeFormFieldSU h hC φ y * y⁻¹ : gramSU h _) :
        primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  rw [primeFormFieldAut_mk, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem mem_gramSU_one_iff (h : UnitaryFieldData 2 f K) (g : GL (Fin 3) K) :
    g ∈ gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ↔
      ((g : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * g = 1 ∧
        (g : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [mem_gramSU, Units.val_one, Matrix.mul_one]

section Diagonal

variable (h : UnitaryFieldData 2 f K)

theorem exists_unit_orderOf_eq_pow_add_one :
    ∃ a : Kˣ, orderOf a = 2 ^ f + 1 ∧ h.bar (a : K) = (a : K)⁻¹ := by
  have := h.finite
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hou : orderOf u = 2 ^ (2 * f) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_units, h.card]
  have hf := h.one_le
  have h2 : 2 ≤ 2 ^ f := le_self_pow₀ (by norm_num) (by omega)
  have hfac : 2 ^ (2 * f) - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
    have e := Nat.sq_sub_sq (2 ^ f) 1
    rw [one_pow, ← pow_mul, mul_comm f 2] at e
    rw [e, mul_comm]
  have hdvd : 2 ^ f - 1 ∣ orderOf u := by rw [hou, hfac]; exact dvd_mul_right _ _
  have hord : orderOf (u ^ (2 ^ f - 1)) = 2 ^ f + 1 := by
    rw [orderOf_pow_of_dvd (by omega) hdvd, hou, hfac,
      Nat.mul_div_cancel_left _ (by omega : 0 < 2 ^ f - 1)]
  refine ⟨u ^ (2 ^ f - 1), hord, ?_⟩
  have hpow : (u ^ (2 ^ f - 1)) ^ (2 ^ f + 1) = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hK : ((u ^ (2 ^ f - 1) : Kˣ) : K) ^ (2 ^ f) * ((u ^ (2 ^ f - 1) : Kˣ) : K) = 1 := by
    rw [← pow_succ, ← Units.val_pow_eq_pow_val, hpow, Units.val_one]
  rw [UnitaryFieldData.bar_apply]
  exact eq_inv_of_mul_eq_one_left hK

@[expose] noncomputable def diagUnit (a : Kˣ) : GL (Fin 3) K where
  val := diagonal ![(a : K), (a⁻¹ : Kˣ), 1]
  inv := diagonal ![((a⁻¹ : Kˣ) : K), (a : K), 1]
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp

theorem coe_diagUnit (a : Kˣ) :
    ((diagUnit a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(a : K), (a⁻¹ : Kˣ), 1] := rfl

theorem coe_diagUnit_inv (a : Kˣ) :
    (((diagUnit a)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![((a⁻¹ : Kˣ) : K), (a : K), 1] := rfl

include h in
theorem diagUnit_mem_gramSU {a : Kˣ} (ha : h.bar (a : K) = (a : K)⁻¹) :
    diagUnit a ∈ gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [mem_gramSU_one_iff, coe_diagUnit, diagonal_map (map_zero h.bar), diagonal_transpose,
    diagonal_mul_diagonal, det_diagonal, Fin.prod_univ_three, ← diagonal_one]
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  refine ⟨?_, by simp⟩
  congr 1
  ext i
  fin_cases i
  · simp [ha, ha0]
  · simp [map_inv₀, ha, ha0]
  · simp

theorem dvd_orderOf_fieldAut_mul_inv_diag (hC : IsPrimeFormGram (1 : GL (Fin 3) K))
    (φ : K ≃+* K) (hφ : ∀ c, φ c = h.bar c) :
    ∃ x : primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
      2 ^ f + 1 ∣ orderOf (primeFormFieldAut h hC φ x * x⁻¹) := by
  obtain ⟨a, hao, ha⟩ := exists_unit_orderOf_eq_pow_add_one h
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  set y : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    ⟨diagUnit a, diagUnit_mem_gramSU h ha⟩
  refine ⟨y, ?_⟩
  rw [fieldAut_mk_mul_inv]
  refine dvd_orderOf_mk_of_forall_scalar h _ fun k c hk => ?_
  have hmat : (((primeFormFieldSU h hC φ y * y⁻¹ : gramSU h _) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal ![(a : K)⁻¹ ^ 2, (a : K) ^ 2, 1] := by
    change ((glAut φ (diagUnit a) * (diagUnit a)⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = _
    rw [Units.val_mul, coe_glAut, coe_diagUnit, coe_diagUnit_inv, diagonal_map (map_zero φ),
      diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i
    · simp [hφ, ha, sq]
    · simp [hφ, ha, map_inv₀, sq]
    · simp
  have hk' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hk
  simp only [Units.val_pow_eq_pow_val, hmat, diagonal_pow, GeneralLinearGroup.coe_scalar] at hk'
  have h22 := congrFun (congrFun hk' 2) 2
  have h11 := congrFun (congrFun hk' 1) 1
  simp only [diagonal_apply_eq, scalar_apply, Pi.pow_apply] at h22 h11
  simp only [Matrix.cons_val_two, Matrix.cons_val_one, Matrix.head_cons, one_pow,
    Matrix.cons_val_zero, Matrix.tail_cons] at h22 h11
  rw [← h22] at h11
  have hak : a ^ (2 * k) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_mul, ← h11]
  have hdvd : 2 ^ f + 1 ∣ 2 * k := hao ▸ orderOf_dvd_of_pow_eq_one hak
  have hodd : Nat.Coprime (2 ^ f + 1) 2 := by
    rw [Nat.coprime_two_right]
    exact (Nat.even_pow.mpr ⟨even_two, by have := h.one_le; omega⟩).add_one
  exact hodd.dvd_of_dvd_mul_left hdvd

end Diagonal

end CFSG.RankThree.PartTwo.Sec20
