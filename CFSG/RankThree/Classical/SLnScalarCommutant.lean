module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.Classical

open scoped Matrix

variable {M : Type*} [Field M]

@[expose] def naturalSL (k : Subfield M) (n : ℕ) : Subgroup (GL (Fin n) M) :=
  (Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map k.subtype)).range

theorem exists_elementary_mem_naturalSL (k : Subfield M) {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ∃ X ∈ naturalSL k n, (X : Matrix (Fin n) (Fin n) M) = 1 + Matrix.single i j 1 := by
  refine ⟨Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map k.subtype
    (⟨Matrix.transvection i j 1, Matrix.det_transvection_of_ne i j hij 1⟩ :
      Matrix.SpecialLinearGroup (Fin n) k)), ⟨_, rfl⟩, ?_⟩
  change (Matrix.transvection i j (1 : k)).map k.subtype = 1 + Matrix.single i j 1
  ext a b
  simp only [Matrix.map_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp

theorem mem_range_scalar_of_commute_elementary {n : ℕ} (A : GL (Fin n) M)
    (h : ∀ i j : Fin n, i ≠ j →
      (1 + Matrix.single i j 1 : Matrix (Fin n) (Fin n) M) * (A : Matrix (Fin n) (Fin n) M) =
        (A : Matrix (Fin n) (Fin n) M) * (1 + Matrix.single i j 1)) :
    A ∈ (Matrix.GeneralLinearGroup.scalar (Fin n)).range := by
  have hcomm : Pairwise fun i j =>
      Commute (Matrix.single i j (1 : M)) (A : Matrix (Fin n) (Fin n) M) := by
    intro i j hij
    have h1 := h i j hij
    rw [add_mul, mul_add, one_mul, mul_one] at h1
    exact add_left_cancel h1
  obtain ⟨a, ha⟩ := Matrix.mem_range_scalar_of_commute_single hcomm
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · refine ⟨1, Units.ext ?_⟩
    ext i
    exact hn.elim i
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hdet := Matrix.GeneralLinearGroup.det_ne_zero A
    rw [← ha, map_zero, Matrix.det_zero] at hdet
    exact hdet rfl
  refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
  exact ha

theorem centralizer_naturalSL (k : Subfield M) {n : ℕ} (_hn : 3 ≤ n) :
    Subgroup.centralizer (naturalSL k n : Set (GL (Fin n) M)) =
      (Matrix.GeneralLinearGroup.scalar (Fin n)).range := by
  ext A
  constructor
  · intro hA
    refine mem_range_scalar_of_commute_elementary A fun i j hij => ?_
    obtain ⟨X, hX, hXe⟩ := exists_elementary_mem_naturalSL k hij
    have h := congrArg Units.val (Subgroup.mem_centralizer_iff.mp hA X hX)
    rw [Units.val_mul, Units.val_mul, hXe] at h
    exact h
  · rintro ⟨a, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun X _ => Units.ext ?_
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute (a : M) (fun r => Commute.all _ r) _).eq.symm

theorem apply_eq_zero_of_conj_inv_transpose_elementary {n : ℕ} (A : GL (Fin n) M) {i j : Fin n}
    (h : (A : Matrix (Fin n) (Fin n) M) * (1 - Matrix.single j i 1) *
      (↑A⁻¹ : Matrix (Fin n) (Fin n) M) = 1 + Matrix.single i j 1) {l : Fin n} (hl : l ≠ i) :
    (A : Matrix (Fin n) (Fin n) M) l j = 0 := by
  have h2 : (A : Matrix (Fin n) (Fin n) M) * (1 - Matrix.single j i 1) =
      (1 + Matrix.single i j 1) * (A : Matrix (Fin n) (Fin n) M) := by
    rw [← h, Matrix.mul_assoc _ (↑A⁻¹ : Matrix (Fin n) (Fin n) M), A.inv_mul, Matrix.mul_one]
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at h2
  have h3 := congrFun (congrFun h2 l) i
  have h4 : (Matrix.single i j (1 : M) * (A : Matrix (Fin n) (Fin n) M)) l i = 0 :=
    Matrix.single_mul_apply_of_ne (h := hl) ..
  rw [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_single_apply_same, h4] at h3
  linear_combination -h3

theorem not_exists_conj_inv_transpose_naturalSL (k : Subfield M) {n : ℕ} (hn : 3 ≤ n) :
    ¬ ∃ A : GL (Fin n) M, ∀ X ∈ naturalSL k n,
      (A : Matrix (Fin n) (Fin n) M) * (↑X⁻¹ : Matrix (Fin n) (Fin n) M)ᵀ *
        (↑A⁻¹ : Matrix (Fin n) (Fin n) M) = X := by
  rintro ⟨A, hA⟩
  have hcol : ∀ i j : Fin n, i ≠ j → ∀ l, l ≠ i → (A : Matrix (Fin n) (Fin n) M) l j = 0 := by
    intro i j hij l hl
    obtain ⟨X, hX, hXe⟩ := exists_elementary_mem_naturalSL k hij
    have hXinv : (↑X⁻¹ : Matrix (Fin n) (Fin n) M) = 1 - Matrix.single i j 1 := by
      rw [Matrix.coe_units_inv, hXe]
      apply Matrix.inv_eq_left_inv
      rw [sub_mul, one_mul, mul_add, mul_one, Matrix.single_mul_single_of_ne (h := hij.symm)]
      abel
    have h := hA X hX
    rw [hXinv, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_single, hXe] at h
    exact apply_eq_zero_of_conj_inv_transpose_elementary A h hl
  have h0 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h1 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h2 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have hzero : ∀ l, (A : Matrix (Fin n) (Fin n) M) l ⟨0, by omega⟩ = 0 := by
    intro l
    by_cases hl : l = ⟨1, by omega⟩
    · subst hl
      exact hcol _ _ h1.symm _ h2
    · exact hcol _ _ h0.symm _ hl
  exact Matrix.GeneralLinearGroup.det_ne_zero A (Matrix.det_eq_zero_of_column_eq_zero _ hzero)

end CFSG.RankThree.Classical
