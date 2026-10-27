module

public import CFSG.Quasithin.Vol2.Ch4Sec3SL3
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBGraphForm
open scoped commutatorElement

namespace KGSL3

variable {F : Type} [Field F]

theorem mem_flagSpace_two {v : Fin 3 → F} : v ∈ flagSpace 3 F 2 ↔ v 2 = 0 := by
  rw [mem_flagSpace]
  constructor
  · intro h
    exact h 2 (by simp)
  · intro h j hj
    have : j = 2 := by
      ext
      have := j.2
      simp only [Fin.val_two]
      omega
    rw [this]
    exact h

theorem entries_of_stab {M : Matrix (Fin 3) (Fin 3) F}
    (h : ∀ w ∈ flagSpace 3 F 2, M.mulVec w ∈ flagSpace 3 F 2) : M 2 0 = 0 ∧ M 2 1 = 0 := by
  have h0 := h (Pi.single 0 1) (mem_flagSpace_two.2 (by simp))
  have h1 := h (Pi.single 1 1) (mem_flagSpace_two.2 (by simp))
  rw [mem_flagSpace_two] at h0 h1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
  exact ⟨h0, h1⟩

theorem stab_of_entries {M : Matrix (Fin 3) (Fin 3) F} (h0 : M 2 0 = 0) (h1 : M 2 1 = 0) :
    ∀ w ∈ flagSpace 3 F 2, M.mulVec w ∈ flagSpace 3 F 2 := by
  intro w hw
  rw [mem_flagSpace_two] at hw ⊢
  simp [mulVec, dotProduct, Fin.sum_univ_three, h0, h1, hw]

@[expose] def uMat (c₀ c₁ : F) : Matrix (Fin 3) (Fin 3) F := !![1, 0, c₀; 0, 1, c₁; 0, 0, 1]

theorem det_uMat (c₀ c₁ : F) : (uMat c₀ c₁).det = 1 := by
  rw [det_fin_three]
  simp [uMat]

@[expose] def uSL (c₀ c₁ : F) : SpecialLinearGroup (Fin 3) F := ⟨uMat c₀ c₁, det_uMat c₀ c₁⟩

@[expose] def mMat (p q r s : F) : Matrix (Fin 3) (Fin 3) F := !![p, q, 0; r, s, 0; 0, 0, 1]

theorem det_mMat (p q r s : F) : (mMat p q r s).det = p * s - q * r := by
  rw [det_fin_three]
  simp [mMat]

@[expose] def mSL (p q r s : F) (h : p * s - q * r = 1) : SpecialLinearGroup (Fin 3) F :=
  ⟨mMat p q r s, (det_mMat p q r s).trans h⟩

theorem mMat_mul_uMat (p q r s c₀ c₁ : F) :
    mMat p q r s * uMat c₀ c₁ = uMat (p * c₀ + q * c₁) (r * c₀ + s * c₁) * mMat p q r s := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mMat, uMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem uMat_mul_uMat (c₀ c₁ d₀ d₁ : F) : uMat c₀ c₁ * uMat d₀ d₁ = uMat (c₀ + d₀) (c₁ + d₁) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uSL_mul_uSL (c₀ c₁ d₀ d₁ : F) : uSL c₀ c₁ * uSL d₀ d₁ = uSL (c₀ + d₀) (c₁ + d₁) :=
  Subtype.ext (uMat_mul_uMat c₀ c₁ d₀ d₁)

theorem uSL_zero : (uSL 0 0 : SpecialLinearGroup (Fin 3) F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL, uMat]

@[expose] def uSub : Subgroup (SpecialLinearGroup (Fin 3) F) where
  carrier := {g | ∃ c₀ c₁ : F, g = uSL c₀ c₁}
  one_mem' := ⟨0, 0, uSL_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨c₀, c₁, rfl⟩ ⟨d₀, d₁, rfl⟩
    exact ⟨c₀ + d₀, c₁ + d₁, uSL_mul_uSL _ _ _ _⟩
  inv_mem' := by
    rintro _ ⟨c₀, c₁, rfl⟩
    refine ⟨-c₀, -c₁, ?_⟩
    apply inv_eq_of_mul_eq_one_right
    rw [uSL_mul_uSL, add_neg_cancel, add_neg_cancel, uSL_zero]

theorem uSub_comm {a b : SpecialLinearGroup (Fin 3) F} (ha : a ∈ uSub) (hb : b ∈ uSub) :
    a * b = b * a := by
  obtain ⟨c₀, c₁, rfl⟩ := ha
  obtain ⟨d₀, d₁, rfl⟩ := hb
  rw [uSL_mul_uSL, uSL_mul_uSL, add_comm c₀, add_comm c₁]

theorem mul_uMat_of_row {y : Matrix (Fin 3) (Fin 3) F} (h0 : y 2 0 = 0) (h1 : y 2 1 = 0)
    (h2 : y 2 2 = 1) (c₀ c₁ : F) :
    y * uMat c₀ c₁ = uMat (y 0 0 * c₀ + y 0 1 * c₁) (y 1 0 * c₀ + y 1 1 * c₁) * y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_three, h0, h1, h2] <;> ring

theorem eq_uSL_of_entries {g : SpecialLinearGroup (Fin 3) F}
    (h0 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (h1 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0)
    (h2 : (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1)
    (h00 : (g : Matrix (Fin 3) (Fin 3) F) 0 0 = 1) (h01 : (g : Matrix (Fin 3) (Fin 3) F) 0 1 = 0)
    (h10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0) (h11 : (g : Matrix (Fin 3) (Fin 3) F) 1 1 = 1) :
    g = uSL ((g : Matrix (Fin 3) (Fin 3) F) 0 2) ((g : Matrix (Fin 3) (Fin 3) F) 1 2) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL, uMat, h0, h1, h2, h00, h01, h10, h11]

theorem uSL_inv (c₀ c₁ : F) : (uSL c₀ c₁)⁻¹ = uSL (-c₀) (-c₁) := by
  apply inv_eq_of_mul_eq_one_right
  rw [uSL_mul_uSL, add_neg_cancel, add_neg_cancel, uSL_zero]

@[expose] def blk (M : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  !![M 0 0, M 0 1; M 1 0, M 1 1]

theorem blk_mul (M : Matrix (Fin 3) (Fin 3) F) {N : Matrix (Fin 3) (Fin 3) F} (h0 : N 2 0 = 0)
    (h1 : N 2 1 = 0) : blk (M * N) = blk M * blk N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_three, h0, h1]

theorem blk_one : blk (1 : Matrix (Fin 3) (Fin 3) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

theorem blk_mul_self [CharP F 2] {M : Matrix (Fin 3) (Fin 3) F} (h0 : M 2 0 = 0)
    (h1 : M 2 1 = 0) (h2 : M 2 2 = 1) (hdet : M.det = 1)
    (hD : (M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0 = 0) : blk M * blk M = 1 := by
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [det_fin_three, h0, h1, h2] at hdet
  have ht : M 0 0 + M 1 1 = 0 := by linear_combination hdet - hD + h2F
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, Matrix.mul_apply]
  · linear_combination M 0 0 * ht - hdet - h2F
  · linear_combination M 0 1 * ht
  · linear_combination M 1 0 * ht
  · linear_combination M 1 1 * ht - hdet - h2F

theorem mem_uSub_of_blk {g : SpecialLinearGroup (Fin 3) F}
    (h0 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (h1 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0)
    (h2 : (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1) (hb : blk (g : Matrix (Fin 3) (Fin 3) F) = 1) :
    g ∈ uSub := by
  have e : ∀ i j : Fin 2,
      blk (g : Matrix (Fin 3) (Fin 3) F) i j = (1 : Matrix (Fin 2) (Fin 2) F) i j :=
    fun i j => by rw [hb]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp [blk] at e00 e01 e10 e11
  exact ⟨_, _, eq_uSL_of_entries h0 h1 h2 e00 e01 e10 e11⟩

section Perfect

variable {Y : Subgroup (SpecialLinearGroup (Fin 3) F)}

theorem rows_of_perfect (hY : ⁅Y, Y⁆ = Y)
    (hstab : ∀ y ∈ Y, ∀ w ∈ flagSpace 3 F 2,
      (y : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ flagSpace 3 F 2)
    {y : SpecialLinearGroup (Fin 3) F} (hy : y ∈ Y) :
    (y : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (y : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧
      (y : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
  obtain ⟨h0, h1⟩ := entries_of_stab (hstab y hy)
  refine ⟨h0, h1, ?_⟩
  have hY' : ⁅Y.map Matrix.SpecialLinearGroup.toGL, Y.map Matrix.SpecialLinearGroup.toGL⁆ =
      Y.map Matrix.SpecialLinearGroup.toGL := by
    rw [← Subgroup.map_commutator, hY]
  have h := mulVec_sub_mem_of_perfect (flagSpace 3 F 2) (finrank_flagSpace (by norm_num))
    (Y.map Matrix.SpecialLinearGroup.toGL) hY' (by
      rintro _ ⟨z, hz, rfl⟩ w hw
      exact hstab z hz w hw) (Subgroup.mem_map_of_mem _ hy) (Pi.single 2 1)
  rw [mem_flagSpace_two] at h
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, sub_eq_zero,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using h

theorem exists_det_sub_ne_zero [CharP F 2] (hY1 : Y ≠ ⊥) (hY : ⁅Y, Y⁆ = Y)
    (hrows : ∀ y ∈ Y, (y : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      (y : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧ (y : Matrix (Fin 3) (Fin 3) F) 2 2 = 1) :
    ∃ y ∈ Y, ((y : Matrix (Fin 3) (Fin 3) F) 0 0 - 1) * ((y : Matrix (Fin 3) (Fin 3) F) 1 1 - 1) -
      (y : Matrix (Fin 3) (Fin 3) F) 0 1 * (y : Matrix (Fin 3) (Fin 3) F) 1 0 ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_and, ne_eq, not_not] at hcon
  have hsq : ∀ y ∈ Y,
      blk (y : Matrix (Fin 3) (Fin 3) F) * blk (y : Matrix (Fin 3) (Fin 3) F) = 1 := by
    intro y hy
    obtain ⟨h0, h1, h2⟩ := hrows y hy
    exact blk_mul_self h0 h1 h2 y.2 (hcon y hy)
  have hinv : ∀ y ∈ Y, blk ((y⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      blk (y : Matrix (Fin 3) (Fin 3) F) := by
    intro y hy
    obtain ⟨h0, h1, -⟩ := hrows _ (Y.inv_mem hy)
    have e : blk (y : Matrix (Fin 3) (Fin 3) F) *
        blk ((y⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← blk_mul _ h0 h1, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, blk_one]
    calc blk ((y⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
        = (blk (y : Matrix (Fin 3) (Fin 3) F) * blk (y : Matrix (Fin 3) (Fin 3) F)) *
            blk ((y⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
          rw [hsq y hy, Matrix.one_mul]
      _ = blk (y : Matrix (Fin 3) (Fin 3) F) := by rw [Matrix.mul_assoc, e, Matrix.mul_one]
  have hcomm : ∀ a ∈ Y, ∀ b ∈ Y, ⁅a, b⁆ ∈ uSub := by
    intro a ha b hb
    have hc : ⁅a, b⁆ ∈ Y := by
      have := Subgroup.commutator_mem_commutator ha hb
      rwa [hY] at this
    obtain ⟨c0, c1, c2⟩ := hrows _ hc
    refine mem_uSub_of_blk c0 c1 c2 ?_
    obtain ⟨b0, b1, -⟩ := hrows b hb
    obtain ⟨ai0, ai1, -⟩ := hrows _ (Y.inv_mem ha)
    obtain ⟨bi0, bi1, -⟩ := hrows _ (Y.inv_mem hb)
    have hab := hsq (a * b) (Y.mul_mem ha hb)
    rw [Matrix.SpecialLinearGroup.coe_mul, blk_mul _ b0 b1] at hab
    rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, blk_mul _ bi0 bi1,
      blk_mul _ ai0 ai1, blk_mul _ b0 b1,
      hinv a ha, hinv b hb]
    simpa only [Matrix.mul_assoc] using hab
  have hle : Y ≤ uSub := by
    rw [← hY]
    exact Subgroup.commutator_le.2 hcomm
  apply hY1
  rw [← hY, eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact uSub_comm (hle ha) (hle hb)

theorem exists_uSL_mem (hY1 : Y ≠ ⊥)
    (hrows : ∀ y ∈ Y, (y : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      (y : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧ (y : Matrix (Fin 3) (Fin 3) F) 2 2 = 1)
    (hnorm : ∀ g : SpecialLinearGroup (Fin 3) F, (∀ w ∈ flagSpace 3 F 2,
      (g : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ flagSpace 3 F 2) →
        g ∈ Subgroup.normalizer (Y : Set (SpecialLinearGroup (Fin 3) F))) :
    ∃ c₀ c₁ : F, (c₀ ≠ 0 ∨ c₁ ≠ 0) ∧ uSL c₀ c₁ ∈ Y := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  apply hY1
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  obtain ⟨h0, h1, h2⟩ := hrows y hy
  have key : ∀ c₀ c₁ : F,
      uSL ((y : Matrix (Fin 3) (Fin 3) F) 0 0 * c₀ + (y : Matrix (Fin 3) (Fin 3) F) 0 1 * c₁ + -c₀)
        ((y : Matrix (Fin 3) (Fin 3) F) 1 0 * c₀ + (y : Matrix (Fin 3) (Fin 3) F) 1 1 * c₁ + -c₁)
        ∈ Y := by
    intro c₀ c₁
    have hu : uSL c₀ c₁ ∈ Subgroup.normalizer (Y : Set (SpecialLinearGroup (Fin 3) F)) :=
      hnorm _ (stab_of_entries (by simp [uSL, uMat]) (by simp [uSL, uMat]))
    have h3 := Y.mul_mem hy ((Subgroup.mem_normalizer_iff.1 hu _).1 (Y.inv_mem hy))
    have hyu : y * uSL c₀ c₁ * y⁻¹ =
        uSL ((y : Matrix (Fin 3) (Fin 3) F) 0 0 * c₀ + (y : Matrix (Fin 3) (Fin 3) F) 0 1 * c₁)
          ((y : Matrix (Fin 3) (Fin 3) F) 1 0 * c₀ + (y : Matrix (Fin 3) (Fin 3) F) 1 1 * c₁) := by
      rw [mul_inv_eq_iff_eq_mul]
      exact Subtype.ext (mul_uMat_of_row h0 h1 h2 c₀ c₁)
    have e : y * (uSL c₀ c₁ * y⁻¹ * (uSL c₀ c₁)⁻¹) =
        uSL ((y : Matrix (Fin 3) (Fin 3) F) 0 0 * c₀ + (y : Matrix (Fin 3) (Fin 3) F) 0 1 * c₁ +
            -c₀)
          ((y : Matrix (Fin 3) (Fin 3) F) 1 0 * c₀ + (y : Matrix (Fin 3) (Fin 3) F) 1 1 * c₁ +
            -c₁) := by
      rw [uSL_inv, ← uSL_mul_uSL, ← hyu]
      group
    rwa [e] at h3
  have hfix : ∀ c₀ c₁ : F,
      (y : Matrix (Fin 3) (Fin 3) F) 0 0 * c₀ + (y : Matrix (Fin 3) (Fin 3) F) 0 1 * c₁ + -c₀ = 0 ∧
        (y : Matrix (Fin 3) (Fin 3) F) 1 0 * c₀ + (y : Matrix (Fin 3) (Fin 3) F) 1 1 * c₁ + -c₁ =
          0 := by
    intro c₀ c₁
    by_contra hne
    rw [not_and_or] at hne
    exact hcon _ _ hne (key c₀ c₁)
  obtain ⟨e00, e10⟩ := hfix 1 0
  obtain ⟨e01, e11⟩ := hfix 0 1
  have hyU := eq_uSL_of_entries h0 h1 h2 (by linear_combination e00) (by linear_combination e01)
    (by linear_combination e10) (by linear_combination e11)
  by_cases hc : (y : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧ (y : Matrix (Fin 3) (Fin 3) F) 1 2 = 0
  · calc y = uSL ((y : Matrix (Fin 3) (Fin 3) F) 0 2) ((y : Matrix (Fin 3) (Fin 3) F) 1 2) := hyU
      _ = uSL 0 0 := by rw [hc.1, hc.2]
      _ = 1 := uSL_zero
  · exfalso
    rw [not_and_or] at hc
    apply hcon _ _ hc
    rw [← hyU]
    exact hy

theorem uSL_conj_mem
    (hnorm : ∀ g : SpecialLinearGroup (Fin 3) F, (∀ w ∈ flagSpace 3 F 2,
      (g : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ flagSpace 3 F 2) →
        g ∈ Subgroup.normalizer (Y : Set (SpecialLinearGroup (Fin 3) F)))
    {c₀ c₁ : F} (hc : uSL c₀ c₁ ∈ Y) (p q r s : F) (h : p * s - q * r = 1) :
    uSL (p * c₀ + q * c₁) (r * c₀ + s * c₁) ∈ Y := by
  have hm : mSL p q r s h ∈ Subgroup.normalizer (Y : Set (SpecialLinearGroup (Fin 3) F)) :=
    hnorm _ (stab_of_entries (by simp [mSL, mMat]) (by simp [mSL, mMat]))
  have h1 := (Subgroup.mem_normalizer_iff.1 hm _).1 hc
  have e : mSL p q r s h * uSL c₀ c₁ * (mSL p q r s h)⁻¹ =
      uSL (p * c₀ + q * c₁) (r * c₀ + s * c₁) := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subtype.ext (mMat_mul_uMat p q r s c₀ c₁)
  rwa [e] at h1

theorem uSL_mem_all (hY1 : Y ≠ ⊥)
    (hrows : ∀ y ∈ Y, (y : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      (y : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧ (y : Matrix (Fin 3) (Fin 3) F) 2 2 = 1)
    (hnorm : ∀ g : SpecialLinearGroup (Fin 3) F, (∀ w ∈ flagSpace 3 F 2,
      (g : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ flagSpace 3 F 2) →
        g ∈ Subgroup.normalizer (Y : Set (SpecialLinearGroup (Fin 3) F)))
    (c₀ c₁ : F) : uSL c₀ c₁ ∈ Y := by
  obtain ⟨d₀, d₁, hd, hdY⟩ := exists_uSL_mem hY1 hrows hnorm
  have h10 : uSL 1 0 ∈ Y := by
    by_cases h0 : d₀ = 0
    · have hd₁ : d₁ ≠ 0 := hd.resolve_left (not_not.2 h0)
      have := uSL_conj_mem hnorm hdY 0 d₁⁻¹ (-d₁) 0 (by simp [hd₁])
      simpa [h0, hd₁] using this
    · have := uSL_conj_mem hnorm hdY d₀⁻¹ 0 (-d₁) d₀ (by simp [h0])
      have e1 : d₀⁻¹ * d₀ + 0 * d₁ = 1 := by rw [inv_mul_cancel₀ h0, zero_mul, add_zero]
      have e2 : -d₁ * d₀ + d₀ * d₁ = 0 := by ring
      rwa [e1, e2] at this
  by_cases ha : c₀ = 0
  · by_cases hb : c₁ = 0
    · rw [ha, hb, uSL_zero]
      exact Y.one_mem
    · have := uSL_conj_mem hnorm h10 0 (-c₁⁻¹) c₁ 0 (by simp [hb])
      rw [ha]
      simpa using this
  · have := uSL_conj_mem hnorm h10 c₀ 0 c₁ c₀⁻¹ (by simp [ha])
    simpa using this

end Perfect

theorem eq_of_inv_mul_mem_center {G : Type*} [Group G] {H : Subgroup G} (hH : ⁅H, H⁆ = H)
    (f : G →* G) (hf : ∀ h ∈ H, h⁻¹ * f h ∈ Subgroup.center G) {h : G} (hh : h ∈ H) :
    f h = h := by
  let z : ↥H →* ↥(Subgroup.center G) :=
    { toFun := fun x => ⟨(x : G)⁻¹ * f x, hf x x.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        show ((x * y : ↥H) : G)⁻¹ * f (x * y : ↥H) = ((x : G)⁻¹ * f x) * ((y : G)⁻¹ * f y)
        have hc := Subgroup.mem_center_iff.1 (hf x x.2) ((y : G)⁻¹)
        rw [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev]
        calc (y : G)⁻¹ * (x : G)⁻¹ * (f x * f y)
            = ((y : G)⁻¹ * ((x : G)⁻¹ * f x)) * f y := by group
          _ = ((x : G)⁻¹ * f x) * (y : G)⁻¹ * f y := by rw [hc]
          _ = (x : G)⁻¹ * f x * ((y : G)⁻¹ * f y) := by group }
  have htop : commutator ↥H = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hH)
  have h1 : (⟨h, hh⟩ : ↥H) ∈ z.ker :=
    Abelianization.commutator_subset_ker z (htop ▸ Subgroup.mem_top _)
  rw [MonoidHom.mem_ker] at h1
  have h2 : h⁻¹ * f h = 1 := congrArg Subtype.val h1
  rw [inv_mul_eq_one] at h2
  exact h2.symm

theorem exists_standard [Finite F] (σ : MulAut (SpecialLinearGroup (Fin 3) F)) :
    ∃ (A : GL (Fin 3) F) (φ : F ≃+* F) (ε : ℕ), ε ≤ 1 ∧
      σ = slConjugation 3 F A * slFieldAut (Fin 3) F φ * slGraphAut 3 F ^ ε := by
  obtain ⟨A, φ, ε, hε, hσ⟩ :=
    (automorphism_generation (K := F) (n := 3) le_rfl).2 (descendAut 3 F σ)
  refine ⟨A, φ, ε, hε, ?_⟩
  set θ := slConjugation 3 F A * slFieldAut (Fin 3) F φ * slGraphAut 3 F ^ ε with hθ
  have hd : descendAut 3 F θ = descendAut 3 F σ := by
    rw [hσ, hθ, map_mul, map_mul, map_pow]
    rfl
  have hperf : ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin 3) F)), ⊤⁆ = ⊤ :=
    CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (by norm_num)
  have hone : descendAut 3 F (σ⁻¹ * θ) = 1 := by rw [map_mul, map_inv, hd, inv_mul_cancel]
  have hfix : ∀ g, (σ⁻¹ * θ) g = g := by
    intro g
    refine eq_of_inv_mul_mem_center hperf (σ⁻¹ * θ).toMonoidHom (fun h _ => ?_)
      (Subgroup.mem_top g)
    rw [← scalars_eq_center, ← proj_eq_proj_iff]
    have e := descendAut_proj 3 F (σ⁻¹ * θ) h
    rw [hone, MulAut.one_apply] at e
    exact e
  have h1 : σ⁻¹ * θ = 1 := MulEquiv.ext hfix
  rw [inv_mul_eq_one] at h1
  exact h1

theorem slFieldAut_entry (φ : F ≃+* F) (g : SpecialLinearGroup (Fin 3) F) (i j : Fin 3) :
    ((slFieldAut (Fin 3) F φ g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j =
      φ ((g : Matrix (Fin 3) (Fin 3) F) i j) := rfl

theorem field_uSL (φ : F ≃+* F) (c₀ c₁ : F) :
    slFieldAut (Fin 3) F φ (uSL c₀ c₁) = uSL (φ c₀) (φ c₁) := by
  apply Subtype.ext
  ext i j
  rw [slFieldAut_entry]
  fin_cases i <;> fin_cases j <;> simp [uSL, uMat]

theorem field_graph_uSL (φ : F ≃+* F) (c₀ c₁ : F) :
    ((slFieldAut (Fin 3) F φ (slGraphAut 3 F (uSL c₀ c₁)) : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, 1, 0; -φ c₀, -φ c₁, 1] := by
  ext i j
  rw [slFieldAut_entry, slGraphAut_matrix, uSL_inv]
  fin_cases i <;> fin_cases j <;> simp [uSL, uMat]

theorem mul_eq_of_slConjugation {A : GL (Fin 3) F} {x y : SpecialLinearGroup (Fin 3) F}
    (h : slConjugation 3 F A x = y) :
    (A : Matrix (Fin 3) (Fin 3) F) * (x : Matrix (Fin 3) (Fin 3) F) =
      (y : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) := by
  rw [← h, coe_slConjugation,
    Matrix.mul_assoc ((A : Matrix (Fin 3) (Fin 3) F) * (x : Matrix (Fin 3) (Fin 3) F)),
    Units.inv_mul, Matrix.mul_one]

theorem entries_of_comm_u {a : Matrix (Fin 3) (Fin 3) F}
    (h1 : a * uMat 1 0 = uMat 1 0 * a) (h2 : a * uMat 0 1 = uMat 0 1 * a) :
    a 2 0 = 0 ∧ a 2 1 = 0 ∧ a 1 0 = 0 ∧ a 0 1 = 0 ∧ a 0 0 = a 2 2 ∧ a 1 1 = a 2 2 := by
  have e00 := congrFun (congrFun h1 0) 0
  have e01 := congrFun (congrFun h1 0) 1
  have e02 := congrFun (congrFun h1 0) 2
  have e12 := congrFun (congrFun h1 1) 2
  have f02 := congrFun (congrFun h2 0) 2
  have f12 := congrFun (congrFun h2 1) 2
  simp [uMat, Matrix.mul_apply, Fin.sum_univ_three] at e00 e01 e02 e12 f02 f12
  exact ⟨e00, e01, e12, f02, by linear_combination e02, by linear_combination f12⟩

theorem eq_of_comm_u {a : Matrix (Fin 3) (Fin 3) F} (ha00 : a 0 0 = a 2 2) (ha22 : a 2 2 ≠ 0)
    {l m : F} (h : a * uMat m 0 = uMat l 0 * a) : m = l := by
  have e := congrFun (congrFun h 0) 2
  simp [uMat, Matrix.mul_apply, Fin.sum_univ_three] at e
  have e' : a 2 2 * (m - l) = 0 := by
    rw [ha00] at e
    linear_combination e
  exact sub_eq_zero.1 ((mul_eq_zero.1 e').resolve_left ha22)

theorem top_of_comm {a y : Matrix (Fin 3) (Fin 3) F} (ha10 : a 1 0 = 0) (ha01 : a 0 1 = 0)
    (ha00 : a 0 0 = a 2 2) (ha11 : a 1 1 = a 2 2) (h2 : y 2 2 = 1)
    (hD : (y 0 0 - 1) * (y 1 1 - 1) - y 0 1 * y 1 0 ≠ 0) (h : a * y = y * a) :
    a 0 2 = 0 ∧ a 1 2 = 0 := by
  have e02 := congrFun (congrFun h 0) 2
  have e12 := congrFun (congrFun h 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, ha10, ha01, ha00, ha11, h2] at e02 e12
  have k1 : ((y 0 0 - 1) * (y 1 1 - 1) - y 0 1 * y 1 0) * a 0 2 = 0 := by
    linear_combination (1 - y 1 1) * e02 + y 0 1 * e12
  have k2 : ((y 0 0 - 1) * (y 1 1 - 1) - y 0 1 * y 1 0) * a 1 2 = 0 := by
    linear_combination y 1 0 * e02 + (1 - y 0 0) * e12
  exact ⟨(mul_eq_zero.1 k1).resolve_left hD, (mul_eq_zero.1 k2).resolve_left hD⟩

theorem det_eq_zero_of_graph {a : Matrix (Fin 3) (Fin 3) F}
    (h1 : a * !![1, 0, 0; 0, 1, 0; -1, 0, 1] = uMat 1 0 * a)
    (h2 : a * !![1, 0, 0; 0, 1, 0; 0, -1, 1] = uMat 0 1 * a) : a.det = 0 := by
  have e20 := congrFun (congrFun h1 2) 0
  have e10 := congrFun (congrFun h1 1) 0
  have f01 := congrFun (congrFun h2 0) 1
  simp [uMat, Matrix.mul_apply, Fin.sum_univ_three] at e20 e10 f01
  rw [det_fin_three, e20, e10, f01]
  ring

theorem eq_one_of_conj_field (A : GL (Fin 3) F) (φ : F ≃+* F)
    (hu : ∀ c₀ c₁ : F, slConjugation 3 F A (slFieldAut (Fin 3) F φ (uSL c₀ c₁)) = uSL c₀ c₁)
    {y₀ : SpecialLinearGroup (Fin 3) F} (h2 : (y₀ : Matrix (Fin 3) (Fin 3) F) 2 2 = 1)
    (hD : ((y₀ : Matrix (Fin 3) (Fin 3) F) 0 0 - 1) * ((y₀ : Matrix (Fin 3) (Fin 3) F) 1 1 - 1) -
      (y₀ : Matrix (Fin 3) (Fin 3) F) 0 1 * (y₀ : Matrix (Fin 3) (Fin 3) F) 1 0 ≠ 0)
    (hy₀ : slConjugation 3 F A (slFieldAut (Fin 3) F φ y₀) = y₀) :
    slConjugation 3 F A * slFieldAut (Fin 3) F φ = 1 := by
  have hk : ∀ c₀ c₁ : F, (A : Matrix (Fin 3) (Fin 3) F) * uMat (φ c₀) (φ c₁) =
      uMat c₀ c₁ * (A : Matrix (Fin 3) (Fin 3) F) := by
    intro c₀ c₁
    have := mul_eq_of_slConjugation (hu c₀ c₁)
    rwa [field_uSL] at this
  have e1 := hk 1 0
  have e2 := hk 0 1
  rw [map_one, map_zero] at e1 e2
  obtain ⟨a20, a21, a10, a01, a00, a11⟩ := entries_of_comm_u e1 e2
  have hd : (A : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := by
    intro h
    apply Matrix.GeneralLinearGroup.det_ne_zero A
    rw [det_fin_three, a20, a21, a10, a01, h]
    ring
  have hφ : ∀ x : F, φ x = x := by
    intro x
    have := hk x 0
    rw [map_zero] at this
    exact eq_of_comm_u a00 hd this
  have hF : ∀ g : SpecialLinearGroup (Fin 3) F, slFieldAut (Fin 3) F φ g = g := by
    intro g
    apply Subtype.ext
    ext i j
    rw [slFieldAut_entry, hφ]
  rw [hF] at hy₀
  obtain ⟨a02, a12⟩ := top_of_comm a10 a01 a00 a11 h2 hD (mul_eq_of_slConjugation hy₀)
  have hA : (A : Matrix (Fin 3) (Fin 3) F) =
      scalar (Fin 3) ((A : Matrix (Fin 3) (Fin 3) F) 2 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a20, a21, a10, a01, a00, a11, a02, a12]
  apply MulEquiv.ext
  intro g
  rw [MulAut.mul_apply, hF, MulAut.one_apply]
  apply Subtype.ext
  have hc : (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) := by
    rw [hA]
    exact (scalar_commute _ (fun r' => Commute.all _ r') _).eq
  rw [coe_slConjugation, hc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem not_graph (A : GL (Fin 3) F) (φ : F ≃+* F)
    (h10 : slConjugation 3 F A (slFieldAut (Fin 3) F φ (slGraphAut 3 F (uSL 1 0))) = uSL 1 0)
    (h01 : slConjugation 3 F A (slFieldAut (Fin 3) F φ (slGraphAut 3 F (uSL 0 1))) = uSL 0 1) :
    False := by
  have e1 := mul_eq_of_slConjugation h10
  have e2 := mul_eq_of_slConjugation h01
  rw [field_graph_uSL, map_one, map_zero, neg_zero] at e1 e2
  exact Matrix.GeneralLinearGroup.det_ne_zero A (det_eq_zero_of_graph e1 e2)

theorem eq_one_of_fix [Finite F] [CharP F 2] {Y : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hY1 : Y ≠ ⊥) (hY : ⁅Y, Y⁆ = Y)
    (hstab : ∀ y ∈ Y, ∀ w ∈ flagSpace 3 F 2,
      (y : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ flagSpace 3 F 2)
    (hnorm : ∀ g : SpecialLinearGroup (Fin 3) F, (∀ w ∈ flagSpace 3 F 2,
      (g : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ flagSpace 3 F 2) →
        g ∈ Subgroup.normalizer (Y : Set (SpecialLinearGroup (Fin 3) F)))
    (σ : MulAut (SpecialLinearGroup (Fin 3) F)) (hσ : ∀ y ∈ Y, σ y = y) : σ = 1 := by
  have hrows := fun y (hy : y ∈ Y) => rows_of_perfect hY hstab hy
  have hU := uSL_mem_all hY1 hrows hnorm
  obtain ⟨y₀, hy₀, hD⟩ := exists_det_sub_ne_zero hY1 hY hrows
  obtain ⟨A, φ, ε, hε, rfl⟩ := exists_standard σ
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one] at hσ ⊢
    exact eq_one_of_conj_field A φ (fun c₀ c₁ => hσ _ (hU c₀ c₁)) (hrows y₀ hy₀).2.2 hD
      (hσ y₀ hy₀)
  · exfalso
    rw [pow_one] at hσ
    exact not_graph A φ (hσ _ (hU 1 0)) (hσ _ (hU 0 1))

theorem stab_conj_iff (g₀ x : SpecialLinearGroup (Fin 3) F) :
    (∀ w ∈ (flagSpace 3 F 2).map (mulVecLin (g₀ : Matrix (Fin 3) (Fin 3) F)),
      ((g₀ * x * g₀⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec w ∈
        (flagSpace 3 F 2).map (mulVecLin (g₀ : Matrix (Fin 3) (Fin 3) F))) ↔
      ∀ v ∈ flagSpace 3 F 2, (x : Matrix (Fin 3) (Fin 3) F).mulVec v ∈ flagSpace 3 F 2 := by
  have hinv : ((g₀⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (g₀ : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hc : ∀ v, ((g₀ * x * g₀⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).mulVec ((g₀ : Matrix (Fin 3) (Fin 3) F).mulVec v) =
      (g₀ : Matrix (Fin 3) (Fin 3) F).mulVec ((x : Matrix (Fin 3) (Fin 3) F).mulVec v) := by
    intro v
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_assoc ((g₀ : Matrix (Fin 3) (Fin 3) F) * (x : Matrix (Fin 3) (Fin 3) F)), hinv,
      Matrix.mul_one]
  have hcancel : ∀ v, ((g₀⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
      ((g₀ : Matrix (Fin 3) (Fin 3) F).mulVec v) = v := by
    intro v
    rw [mulVec_mulVec, hinv, one_mulVec]
  constructor
  · intro h v hv
    obtain ⟨v', hv', he⟩ := Submodule.mem_map.1 (h _ (Submodule.mem_map_of_mem hv))
    rw [mulVecLin_apply, mulVecLin_apply, hc] at he
    have := congrArg (((g₀⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec) he
    rw [hcancel, hcancel] at this
    rw [← this]
    exact hv'
  · rintro h _ ⟨v, hv, rfl⟩
    rw [mulVecLin_apply, hc]
    exact Submodule.mem_map_of_mem (h v hv)

end KGSL3

open KGSL3 in
theorem sl3ParabolicAutFact_holds : SL3ParabolicAutFact := by
  intro F _ _ n _hn hcard W hW Y hY1 hY hstab hnorm σ _hσ hfix
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard
  obtain ⟨g₀, hg₀⟩ := exists_map_flagSpace_eq (n := 3) W
  rw [hW] at hg₀
  let ψ : SpecialLinearGroup (Fin 3) F ≃* ↥(StatedSL 3 F) :=
    (MulAut.conj g₀).trans (specialLinearGroupEquivStatedSL 3 F)
  have hst : ∀ x : SpecialLinearGroup (Fin 3) F,
      (∀ w ∈ W, (((ψ x : ↥(StatedSL 3 F)) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W) ↔
        ∀ v ∈ flagSpace 3 F 2, (x : Matrix (Fin 3) (Fin 3) F).mulVec v ∈ flagSpace 3 F 2 := by
    intro x
    rw [← hg₀]
    exact stab_conj_iff g₀ x
  set Y₀ : Subgroup (SpecialLinearGroup (Fin 3) F) := Y.comap ψ.toMonoidHom with hY₀def
  have hY₀1 : Y₀ ≠ ⊥ := by
    intro h
    apply hY1
    rw [eq_bot_iff]
    intro y hy
    have h1 : ψ.symm y ∈ Y₀ := by
      show ψ (ψ.symm y) ∈ Y
      rw [MulEquiv.apply_symm_apply]
      exact hy
    rw [h, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot, ← MulEquiv.apply_symm_apply ψ y, h1, map_one]
  have hY₀ : ⁅Y₀, Y₀⁆ = Y₀ := by
    rw [hY₀def, Subgroup.comap_equiv_eq_map_symm', ← Subgroup.map_commutator, hY]
  have hstab₀ : ∀ y ∈ Y₀, ∀ w ∈ flagSpace 3 F 2,
      (y : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ flagSpace 3 F 2 :=
    fun y hy => (hst y).1 (hstab (ψ y) hy)
  have hnorm₀ : ∀ g : SpecialLinearGroup (Fin 3) F, (∀ w ∈ flagSpace 3 F 2,
      (g : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ flagSpace 3 F 2) →
        g ∈ Subgroup.normalizer (Y₀ : Set (SpecialLinearGroup (Fin 3) F)) := by
    intro g hg
    have hψg := hnorm (ψ g) ((hst g).2 hg)
    rw [Subgroup.mem_normalizer_iff] at hψg ⊢
    intro h
    have := hψg (ψ h)
    rw [← map_inv ψ, ← map_mul ψ, ← map_mul ψ] at this
    exact this
  let σ₀ : MulAut (SpecialLinearGroup (Fin 3) F) := (ψ.trans σ).trans ψ.symm
  have hσ₀ : σ₀ = 1 := eq_one_of_fix hY₀1 hY₀ hstab₀ hnorm₀ σ₀ fun y hy => by
    show ψ.symm (σ (ψ y)) = y
    rw [hfix (ψ y) hy, MulEquiv.symm_apply_apply]
  apply MulEquiv.ext
  intro s
  obtain ⟨x, rfl⟩ := ψ.surjective s
  have h1 : ψ.symm (σ (ψ x)) = x :=
    congrArg (fun τ : MulAut (SpecialLinearGroup (Fin 3) F) => τ x) hσ₀
  rw [MulAut.one_apply]
  calc σ (ψ x) = ψ (ψ.symm (σ (ψ x))) := (MulEquiv.apply_symm_apply ψ _).symm
    _ = ψ x := by rw [h1]

end CFSG.Quasithin.H13.Ch4
