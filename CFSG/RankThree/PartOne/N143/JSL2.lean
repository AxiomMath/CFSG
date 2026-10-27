module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartOne.N143

section Entries

variable {K : Type} [Field K]

abbrev e2 (M : Matrix.SpecialLinearGroup (Fin 2) K) (i j : Fin 2) : K :=
  (M : Matrix (Fin 2) (Fin 2) K) i j

theorem e2_ext {M N : Matrix.SpecialLinearGroup (Fin 2) K} (h : ∀ i j, e2 M i j = e2 N i j) :
    M = N := by
  apply Subtype.ext
  ext i j
  exact h i j

theorem e2_mul (M N : Matrix.SpecialLinearGroup (Fin 2) K) (i j : Fin 2) :
    e2 (M * N) i j = e2 M i 0 * e2 N 0 j + e2 M i 1 * e2 N 1 j := by
  simp only [e2, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem e2_one (i j : Fin 2) :
    e2 (1 : Matrix.SpecialLinearGroup (Fin 2) K) i j = if i = j then 1 else 0 := by
  simp [e2, Matrix.one_apply]

theorem e2_inv_00 (M : Matrix.SpecialLinearGroup (Fin 2) K) : e2 M⁻¹ 0 0 = e2 M 1 1 := by
  simp [e2, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem e2_inv_01 (M : Matrix.SpecialLinearGroup (Fin 2) K) : e2 M⁻¹ 0 1 = - e2 M 0 1 := by
  simp [e2, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem e2_inv_10 (M : Matrix.SpecialLinearGroup (Fin 2) K) : e2 M⁻¹ 1 0 = - e2 M 1 0 := by
  simp [e2, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem e2_inv_11 (M : Matrix.SpecialLinearGroup (Fin 2) K) : e2 M⁻¹ 1 1 = e2 M 0 0 := by
  simp [e2, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem e2_det (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    e2 M 0 0 * e2 M 1 1 - e2 M 0 1 * e2 M 1 0 = 1 := by
  have h := M.2
  rwa [Matrix.det_fin_two] at h

def hmat (ζ : Kˣ) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![(ζ : K), 0; 0, (ζ : K)⁻¹], by
    rw [Matrix.det_fin_two_of]
    simp⟩

theorem e2_hmat_00 (ζ : Kˣ) : e2 (hmat ζ : Matrix.SpecialLinearGroup (Fin 2) K) 0 0 = ζ := by
  simp [e2, hmat]

theorem e2_hmat_01 (ζ : Kˣ) : e2 (hmat ζ : Matrix.SpecialLinearGroup (Fin 2) K) 0 1 = 0 := by
  simp [e2, hmat]

theorem e2_hmat_10 (ζ : Kˣ) : e2 (hmat ζ : Matrix.SpecialLinearGroup (Fin 2) K) 1 0 = 0 := by
  simp [e2, hmat]

theorem e2_hmat_11 (ζ : Kˣ) : e2 (hmat ζ : Matrix.SpecialLinearGroup (Fin 2) K) 1 1 = (ζ : K)⁻¹ := by
  simp [e2, hmat]

theorem e2_conj_hmat (ζ : Kˣ) (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    e2 (hmat ζ * M * (hmat ζ)⁻¹) 0 0 = e2 M 0 0 ∧
    e2 (hmat ζ * M * (hmat ζ)⁻¹) 0 1 = (ζ : K) ^ 2 * e2 M 0 1 ∧
    e2 (hmat ζ * M * (hmat ζ)⁻¹) 1 0 = ((ζ : K)⁻¹) ^ 2 * e2 M 1 0 ∧
    e2 (hmat ζ * M * (hmat ζ)⁻¹) 1 1 = e2 M 1 1 := by
  have hz : (ζ : K) ≠ 0 := ζ.ne_zero
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [e2_mul, e2_inv_00, e2_inv_01, e2_inv_10, e2_inv_11, e2_hmat_00, e2_hmat_01,
      e2_hmat_10, e2_hmat_11] <;>
    field_simp <;> ring

end Entries

section Subgroups

variable (K : Type) [Field K]

def Uplus : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) where
  carrier := {M | e2 M 0 0 = 1 ∧ e2 M 1 0 = 0 ∧ e2 M 1 1 = 1}
  mul_mem' := by
    rintro M N ⟨hM00, hM10, hM11⟩ ⟨hN00, hN10, hN11⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [e2_mul, hM00, hN00, hN10]
      ring
    · simp only [e2_mul, hM10, hM11, hN00, hN10]
      ring
    · simp only [e2_mul, hM10, hM11, hN11]
      ring
  one_mem' := ⟨by simp [e2_one], by simp [e2_one], by simp [e2_one]⟩
  inv_mem' := by
    rintro M ⟨hM00, hM10, hM11⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [e2_inv_00, hM11]
    · rw [e2_inv_10, hM10, neg_zero]
    · rw [e2_inv_11, hM00]

def Uminus : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) where
  carrier := {M | e2 M 0 0 = 1 ∧ e2 M 0 1 = 0 ∧ e2 M 1 1 = 1}
  mul_mem' := by
    rintro M N ⟨hM00, hM01, hM11⟩ ⟨hN00, hN01, hN11⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [e2_mul, hM00, hM01, hN00]
      ring
    · simp only [e2_mul, hM00, hM01, hN01, hN11]
      ring
    · simp only [e2_mul, hM11, hN01, hN11]
      ring
  one_mem' := ⟨by simp [e2_one], by simp [e2_one], by simp [e2_one]⟩
  inv_mem' := by
    rintro M ⟨hM00, hM01, hM11⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [e2_inv_00, hM11]
    · rw [e2_inv_01, hM01, neg_zero]
    · rw [e2_inv_11, hM00]

def Dg : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) where
  carrier := {M | e2 M 0 1 = 0 ∧ e2 M 1 0 = 0}
  mul_mem' := by
    rintro M N ⟨hM01, hM10⟩ ⟨hN01, hN10⟩
    refine ⟨?_, ?_⟩
    · simp only [e2_mul, hM01, hN01]
      ring
    · simp only [e2_mul, hM10, hN10]
      ring
  one_mem' := ⟨by simp [e2_one], by simp [e2_one]⟩
  inv_mem' := by
    rintro M ⟨hM01, hM10⟩
    refine ⟨?_, ?_⟩
    · rw [e2_inv_01, hM01, neg_zero]
    · rw [e2_inv_10, hM10, neg_zero]

variable {K}

def trv : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem trv_mem_Uplus : (trv : Matrix.SpecialLinearGroup (Fin 2) K) ∈ Uplus K :=
  ⟨by simp [e2, trv], by simp [e2, trv], by simp [e2, trv]⟩

theorem trv_ne_one : (trv : Matrix.SpecialLinearGroup (Fin 2) K) ≠ 1 := by
  intro h
  have h1 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K => e2 M 0 1) h
  simp [e2, trv] at h1

theorem Uplus_not_le_Uminus : ¬ Uplus K ≤ Uminus K := by
  intro hle
  have h1 := (hle (trv_mem_Uplus (K := K))).2.1
  simp [e2, trv] at h1

theorem mem_Uplus {M : Matrix.SpecialLinearGroup (Fin 2) K} :
    M ∈ Uplus K ↔ e2 M 0 0 = 1 ∧ e2 M 1 0 = 0 ∧ e2 M 1 1 = 1 := Iff.rfl

theorem mem_Uminus {M : Matrix.SpecialLinearGroup (Fin 2) K} :
    M ∈ Uminus K ↔ e2 M 0 0 = 1 ∧ e2 M 0 1 = 0 ∧ e2 M 1 1 = 1 := Iff.rfl

theorem hmat_mem_Dg (ζ : Kˣ) : (hmat ζ : Matrix.SpecialLinearGroup (Fin 2) K) ∈ Dg K :=
  ⟨e2_hmat_01 ζ, e2_hmat_10 ζ⟩

theorem conj_Uplus_mem {D M : Matrix.SpecialLinearGroup (Fin 2) K} (hD : D ∈ Dg K)
    (hM : M ∈ Uplus K) : D * M * D⁻¹ ∈ Uplus K := by
  obtain ⟨hD01, hD10⟩ := hD
  obtain ⟨hM00, hM10, hM11⟩ := hM
  have hdet := e2_det D
  rw [hD01, hD10] at hdet
  refine ⟨?_, ?_, ?_⟩
  · simp only [e2_mul, e2_inv_00, e2_inv_10, hD01, hD10, hM00, hM10, hM11]
    linear_combination hdet
  · simp only [e2_mul, e2_inv_00, e2_inv_10, hD10, hM00, hM10, hM11]
    ring
  · simp only [e2_mul, e2_inv_01, e2_inv_11, hD01, hD10, hM00, hM10, hM11]
    linear_combination hdet

theorem conj_Uminus_mem {D M : Matrix.SpecialLinearGroup (Fin 2) K} (hD : D ∈ Dg K)
    (hM : M ∈ Uminus K) : D * M * D⁻¹ ∈ Uminus K := by
  obtain ⟨hD01, hD10⟩ := hD
  obtain ⟨hM00, hM01, hM11⟩ := hM
  have hdet := e2_det D
  rw [hD01, hD10] at hdet
  refine ⟨?_, ?_, ?_⟩
  · simp only [e2_mul, e2_inv_00, e2_inv_10, hD01, hD10, hM00, hM01, hM11]
    linear_combination hdet
  · simp only [e2_mul, e2_inv_01, e2_inv_11, hD01, hM00, hM01, hM11]
    ring
  · simp only [e2_mul, e2_inv_01, e2_inv_11, hD01, hD10, hM00, hM01, hM11]
    linear_combination hdet

theorem hmat_pow_conj_Uplus (ζ : Kˣ) (k : ℕ) {M : Matrix.SpecialLinearGroup (Fin 2) K}
    (hM : M ∈ Uplus K) : (hmat ζ) ^ k * M * ((hmat ζ) ^ k)⁻¹ ∈ Uplus K :=
  conj_Uplus_mem (Subgroup.pow_mem _ (hmat_mem_Dg ζ) k) hM

theorem hmat_pow_conj_Uminus (ζ : Kˣ) (k : ℕ) {M : Matrix.SpecialLinearGroup (Fin 2) K}
    (hM : M ∈ Uminus K) : (hmat ζ) ^ k * M * ((hmat ζ) ^ k)⁻¹ ∈ Uminus K :=
  conj_Uminus_mem (Subgroup.pow_mem _ (hmat_mem_Dg ζ) k) hM

end Subgroups

section Char2

variable {K : Type} [Field K] [CharP K 2]

theorem Uplus_sq {M : Matrix.SpecialLinearGroup (Fin 2) K} (hM : M ∈ Uplus K) : M * M = 1 := by
  obtain ⟨h00, h10, h11⟩ := hM
  apply e2_ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [e2_mul, e2_one, h00, h10, h11, CharTwo.add_self_eq_zero]

theorem Uminus_sq {M : Matrix.SpecialLinearGroup (Fin 2) K} (hM : M ∈ Uminus K) : M * M = 1 := by
  obtain ⟨h00, h01, h11⟩ := hM
  apply e2_ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [e2_mul, e2_one, h00, h01, h11, CharTwo.add_self_eq_zero]

theorem e2_tr_zero {g : Matrix.SpecialLinearGroup (Fin 2) K} (hg : g * g = 1) :
    e2 g 0 0 + e2 g 1 1 = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have E1 : e2 g 0 0 * e2 g 0 0 + e2 g 0 1 * e2 g 1 0 = 1 := by
    have h := e2_mul g g 0 0
    rw [hg, e2_one] at h
    simpa using h.symm
  have E2 : e2 g 1 0 * e2 g 0 1 + e2 g 1 1 * e2 g 1 1 = 1 := by
    have h := e2_mul g g 1 1
    rw [hg, e2_one] at h
    simpa using h.symm
  have hdet := e2_det g
  have h : (e2 g 0 0 + e2 g 1 1) ^ 2 = 0 := by
    linear_combination E1 + E2 + 2 * hdet + 2 * h2
  exact (pow_eq_zero_iff two_ne_zero).1 h

theorem sl2_bc_zero {ζ : Kˣ} (hζ : ζ ^ 2 ≠ 1) {W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)}
    (hsq : ∀ M ∈ W, M * M = 1) (hnorm : ∀ M ∈ W, hmat ζ * M * (hmat ζ)⁻¹ ∈ W)
    {M : Matrix.SpecialLinearGroup (Fin 2) K} (hM : M ∈ W) : e2 M 0 1 * e2 M 1 0 = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hg : (hmat ζ * M * (hmat ζ)⁻¹) * M⁻¹ ∈ W := W.mul_mem (hnorm M hM) (W.inv_mem hM)
  have htr := e2_tr_zero (hsq _ hg)
  obtain ⟨c00, c01, c10, c11⟩ := e2_conj_hmat ζ M
  simp only [e2_mul, e2_inv_00, e2_inv_01, e2_inv_10, e2_inv_11, c00, c01, c10, c11] at htr
  have hprod : e2 M 0 1 * e2 M 1 0 * ((ζ : K) ^ 2 + ((ζ : K)⁻¹) ^ 2) = 0 := by
    linear_combination (-1 : K) * htr + (e2 M 0 0 * e2 M 1 1) * h2
  rcases mul_eq_zero.1 hprod with h | h
  · exact h
  · exfalso
    apply hζ
    have hne : (ζ : K) ≠ 0 := ζ.ne_zero
    have h4 : (ζ : K) ^ 4 + 1 = 0 := by
      have e : (ζ : K) ^ 4 + 1 = (ζ : K) ^ 2 * ((ζ : K) ^ 2 + ((ζ : K)⁻¹) ^ 2) := by
        field_simp
      rw [e, h, mul_zero]
    have h5 : ((ζ : K) ^ 2 + 1) ^ 2 = 0 := by linear_combination h4 + (ζ : K) ^ 2 * h2
    have h6 : (ζ : K) ^ 2 + 1 = 0 := (pow_eq_zero_iff two_ne_zero).1 h5
    have h7 : (ζ : K) ^ 2 = 1 := by linear_combination h6 - h2
    exact Units.ext (by simpa using h7)

theorem sl2_unitriangular {M : Matrix.SpecialLinearGroup (Fin 2) K} (hsq : M * M = 1)
    (hbc : e2 M 0 1 * e2 M 1 0 = 0) : M ∈ Uplus K ∨ M ∈ Uminus K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have htr := e2_tr_zero hsq
  have hdet := e2_det M
  have had : e2 M 0 0 * e2 M 1 1 = 1 := by linear_combination hdet + hbc
  have hd : e2 M 1 1 = - e2 M 0 0 := by linear_combination htr
  rw [hd] at had
  have h5 : (e2 M 0 0 + 1) ^ 2 = 0 := by
    linear_combination (-1 : K) * had + (e2 M 0 0) * h2
  have h6 : e2 M 0 0 + 1 = 0 := (pow_eq_zero_iff two_ne_zero).1 h5
  have ha : e2 M 0 0 = 1 := by linear_combination h6 - h2
  have hd1 : e2 M 1 1 = 1 := by linear_combination htr - ha - h2
  rcases mul_eq_zero.1 hbc with hb | hc
  · exact Or.inr ⟨ha, hb, hd1⟩
  · exact Or.inl ⟨ha, hc, hd1⟩

theorem sl2_two_group_cases {ζ : Kˣ} (hζ : ζ ^ 2 ≠ 1)
    {W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} (hsq : ∀ M ∈ W, M * M = 1)
    (hnorm : ∀ M ∈ W, hmat ζ * M * (hmat ζ)⁻¹ ∈ W) : W ≤ Uplus K ∨ W ≤ Uminus K := by
  have hcase : ∀ M ∈ W, M ∈ Uplus K ∨ M ∈ Uminus K := fun M hM =>
    sl2_unitriangular (hsq M hM) (sl2_bc_zero hζ hsq hnorm hM)
  by_contra hcon
  push Not at hcon
  obtain ⟨hnp, hnm⟩ := hcon
  rw [IsConcreteLE.not_le_iff_exists] at hnp hnm
  obtain ⟨M₁, hM₁W, hM₁⟩ := hnp
  obtain ⟨M₂, hM₂W, hM₂⟩ := hnm
  have hM₁m : M₁ ∈ Uminus K := (hcase M₁ hM₁W).resolve_left hM₁
  have hM₂p : M₂ ∈ Uplus K := (hcase M₂ hM₂W).resolve_right hM₂
  rcases hcase (M₁ * M₂) (W.mul_mem hM₁W hM₂W) with h | h
  · apply hM₁
    have : M₁ = (M₁ * M₂) * M₂⁻¹ := by group
    rw [this]
    exact (Uplus K).mul_mem h ((Uplus K).inv_mem hM₂p)
  · apply hM₂
    have : M₂ = M₁⁻¹ * (M₁ * M₂) := by group
    rw [this]
    exact (Uminus K).mul_mem ((Uminus K).inv_mem hM₁m) h

end Char2

end CFSG.RankThree.PartOne.N143
