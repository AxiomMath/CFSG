module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofSU3Kind

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item812Res11

open CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial Matrix
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof (fourierMat)

@[expose] def U38Witness (M : Type*) [Group M] : Prop :=
  ∃ u s : M, u ^ 4 = 1 ∧ s ^ 4 = 1 ∧ (u ^ 2 * (s * u ^ 2 * s⁻¹)) ^ 3 = 1 ∧
    u ^ 2 * (s * u ^ 2 * s⁻¹) ≠ 1

theorem U38Witness.of_mulEquiv {M M' : Type*} [Group M] [Group M'] (e : M ≃* M')
    (h : U38Witness M') : U38Witness M := by
  obtain ⟨u, s, hu, hs, hw3, hw1⟩ := h
  have key : e.symm u ^ 2 * (e.symm s * e.symm u ^ 2 * (e.symm s)⁻¹) =
      e.symm (u ^ 2 * (s * u ^ 2 * s⁻¹)) := by
    simp only [map_mul, map_pow, map_inv]
  refine ⟨e.symm u, e.symm s, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hu, map_one]
  · rw [← map_pow, hs, map_one]
  · rw [key, ← map_pow, hw3, map_one]
  · rw [key]
    intro h1
    exact hw1 (e.symm.injective (h1.trans (map_one e.symm).symm))

variable {K : Type} [Field K]

@[expose] def permMat01 (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def permMat12 (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; 0, 0, 1; 0, 1, 0]

@[expose] def permMatW (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem permMat01_mul_self : permMat01 K * permMat01 K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [permMat01, Matrix.mul_apply, Fin.sum_univ_three]

theorem permMat12_mul_self : permMat12 K * permMat12 K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [permMat12, Matrix.mul_apply, Fin.sum_univ_three]

theorem permMat12_mul_conj : permMat12 K * (permMat01 K * permMat12 K * permMat01 K) =
    permMatW K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [permMat01, permMat12, permMatW, Matrix.mul_apply, Fin.sum_univ_three]

theorem permMatW_cube : permMatW K * permMatW K * permMatW K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [permMatW, Matrix.mul_apply, Fin.sum_univ_three]

theorem fourierMat_mul_self [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    fourierMat ω * fourierMat ω = permMat12 K := by
  have h2F : (2 : K) = 0 := CharTwo.two_eq_zero
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω4 : ω ^ 4 = ω := by linear_combination (ω ^ 2 - ω) * hω
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourierMat, permMat12, Matrix.mul_apply, Fin.sum_univ_three] <;>
    grind

theorem exists_gl_witness (h : UnitaryFieldData 2 1 K) :
    ∃ U S : GL (Fin 3) K, U ∈ CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 1) K ∧
      S ∈ CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 1) K ∧ U ^ 4 = 1 ∧ S ^ 4 = 1 ∧
      (U ^ 2 * (S * U ^ 2 * S⁻¹)) ^ 3 = 1 ∧
      U ^ 2 * (S * U ^ 2 * S⁻¹) ∉ Subgroup.center (GL (Fin 3) K) := by
  have : CharP K 2 := h.charP
  obtain ⟨ω, hω, hbar⟩ := CFSG.RankThree.PartOne.SEITZQ1.q1_exists_omega h odd_one
  have h2F : (2 : K) = 0 := CharTwo.two_eq_zero
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω4 : ω ^ 4 = ω := by linear_combination (ω ^ 2 - ω) * hω
  have hbar2 : h.bar (ω ^ 2) = ω := by
    rw [map_pow, hbar]
    grind
  have hbar0 : h.bar 0 = 0 := map_zero _
  have hbar1 : h.bar 1 = 1 := map_one _
  have hdetF : (fourierMat ω).det = 1 := by
    rw [fourierMat, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_fin_const]
    grind
  have hdetF0 : (fourierMat ω).det ≠ 0 := by rw [hdetF]; exact one_ne_zero
  have hunitF : ((fourierMat ω).map h.bar)ᵀ * fourierMat ω = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [fourierMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply,
        Matrix.transpose_apply, hbar, hbar2] <;>
      grind
  have hdetP : (permMat01 K).det = 1 := by
    rw [permMat01, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_fin_const]
    grind
  have hdetP0 : (permMat01 K).det ≠ 0 := by rw [hdetP]; exact one_ne_zero
  have hunitP : ((permMat01 K).map h.bar)ᵀ * permMat01 K = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [permMat01, Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply,
        Matrix.transpose_apply, hbar0, hbar1]
  set U : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (fourierMat ω) hdetF0 with hU
  set S : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (permMat01 K) hdetP0 with hS
  have hUv : (U : Matrix (Fin 3) (Fin 3) K) = fourierMat ω := rfl
  have hSv : (S : Matrix (Fin 3) (Fin 3) K) = permMat01 K := rfl
  have hU2 : ((U ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = permMat12 K := by
    rw [Units.val_pow_eq_pow_val, hUv, sq, fourierMat_mul_self hω]
  have hSS : S * S = 1 := by
    apply Units.ext
    rw [Units.val_mul, hSv, permMat01_mul_self, Units.val_one]
  have hSinv : S⁻¹ = S := inv_eq_of_mul_eq_one_left hSS
  have hW : ((U ^ 2 * (S * U ^ 2 * S⁻¹) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      permMatW K := by
    rw [hSinv, Units.val_mul, Units.val_mul, Units.val_mul, hU2, hSv, permMat12_mul_conj]
  refine ⟨U, S, (mem_unitarySU_iff h).mpr ⟨hdetF, hunitF⟩,
    (mem_unitarySU_iff h).mpr ⟨hdetP, hunitP⟩, ?_, ?_, ?_, ?_⟩
  · apply Units.ext
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Units.val_pow_eq_pow_val, hU2, sq,
      permMat12_mul_self, Units.val_one]
  · have hS2 : S ^ 2 = 1 := by rw [sq, hSS]
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hS2, one_pow]
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, hW, pow_three, ← Matrix.mul_assoc, permMatW_cube,
      Units.val_one]
  · rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    rintro ⟨c, hc⟩
    have h1 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 1 0) hc
    simp only [hW] at h1
    simp [permMatW] at h1

theorem u38Witness_statedSU (h : UnitaryFieldData 2 1 K) :
    U38Witness (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 1) K) := by
  obtain ⟨U, S, hU, hS, hU4, hS4, hW3, hW1⟩ := exists_gl_witness h
  refine ⟨⟨U, hU⟩, ⟨S, hS⟩, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, ?_⟩
  · simpa using hU4
  · simpa using hS4
  · simpa using hW3
  · intro h1
    apply hW1
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv, Subgroup.coe_one] at h2
    rw [h2]
    exact Subgroup.one_mem _

theorem u38Witness_pgu (h : UnitaryFieldData 2 1 K) :
    U38Witness (projImage (Sec4.glPi false 3 (2 ^ 1) K)) := by
  obtain ⟨U, S, hU, hS, hU4, hS4, hW3, hW1⟩ := exists_gl_witness h
  have hle : CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 1) K ≤ Sec4.glPi false 3 (2 ^ 1) K :=
    Sec4.slPi_le_glPi (π := false) (fun _ => h)
  set u : projImage (Sec4.glPi false 3 (2 ^ 1) K) :=
    ⟨Matrix.ProjGenLinGroup.mk U, Subgroup.mem_map_of_mem _ (hle hU)⟩ with hu
  set s : projImage (Sec4.glPi false 3 (2 ^ 1) K) :=
    ⟨Matrix.ProjGenLinGroup.mk S, Subgroup.mem_map_of_mem _ (hle hS)⟩ with hs
  have key : ((u ^ 2 * (s * u ^ 2 * s⁻¹) : projImage (Sec4.glPi false 3 (2 ^ 1) K)) :
      Matrix.ProjGenLinGroup (Fin 3) K) =
      Matrix.ProjGenLinGroup.mk (U ^ 2 * (S * U ^ 2 * S⁻¹)) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv, hu, hs, map_mul, map_pow,
      map_inv]
  refine ⟨u, s, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, ?_⟩
  · simp only [Subgroup.coe_pow, hu, Subgroup.coe_one, ← map_pow, hU4, map_one]
  · simp only [Subgroup.coe_pow, hs, Subgroup.coe_one, ← map_pow, hS4, map_one]
  · rw [Subgroup.coe_pow, key, ← map_pow, hW3, map_one, Subgroup.coe_one]
  · intro h1
    apply hW1
    have h2 := congrArg Subtype.val h1
    rw [key, Subgroup.coe_one] at h2
    exact Matrix.ProjGenLinGroup.mk_eq_one.mp h2

end CFSG.RankThree.PartTwo.Sec8.Item812Res11
