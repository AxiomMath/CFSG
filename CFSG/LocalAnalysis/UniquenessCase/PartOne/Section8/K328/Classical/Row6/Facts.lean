module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open Matrix
open scoped commutatorElement

private lemma k328r6f_omega_cube (F : Type) [Field F] (ω : F)
    (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  linear_combination (ω - 1) * hω

private lemma k328r6f_charP (F : Type) [Field F] [Fintype F]
    (hF : Fintype.card F = 64) : CharP F 2 :=
  charP_of_card_eq_prime_pow (p := 2) (f := 6) (by rw [hF]; norm_num)

private lemma k328r6f_omega_ne_one (F : Type) [Field F] [Fintype F]
    (hF : Fintype.card F = 64) (ω : F) (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 1 := by
  have hchar : CharP F 2 := k328r6f_charP F hF
  intro h
  rw [h] at hω
  have h1 : (1 : F) + 1 + 1 = 0 := by simpa using hω
  rw [CharTwo.add_self_eq_zero, zero_add] at h1
  exact one_ne_zero h1

private lemma k328r6f_omega_ne_sq (F : Type) [Field F] [Fintype F]
    (hF : Fintype.card F = 64) (ω : F) (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ ω ^ 2 := by
  have hchar : CharP F 2 := k328r6f_charP F hF
  intro h
  rw [show ω ^ 2 = ω from h.symm] at hω
  have h1 : ω + ω + 1 = 0 := hω
  rw [CharTwo.add_self_eq_zero, zero_add] at h1
  exact one_ne_zero h1

private lemma k328r6f_omega_mul_sq (F : Type) [Field F] (ω : F) (hω3 : ω ^ 3 = 1) :
    ω * ω ^ 2 = 1 := by
  calc ω * ω ^ 2 = ω ^ 3 := by ring
    _ = 1 := hω3

private lemma k328r6f_sq_mul_omega (F : Type) [Field F] (ω : F) (hω3 : ω ^ 3 = 1) :
    ω ^ 2 * ω = 1 := by
  rw [mul_comm, k328r6f_omega_mul_sq F ω hω3]

private lemma k328r6f_omega_sq_cube (F : Type) [Field F] (ω : F) (hω3 : ω ^ 3 = 1) :
    (ω ^ 2) ^ 3 = 1 := by
  calc (ω ^ 2) ^ 3 = (ω ^ 3) ^ 2 := by ring
    _ = 1 := by rw [hω3, one_pow]

private lemma k328r6f_omega8 (F : Type) [Field F] (ω : F) (hω3 : ω ^ 3 = 1) :
    ω ^ 8 = ω ^ 2 := by
  calc ω ^ 8 = (ω ^ 3) ^ 2 * ω ^ 2 := by ring
    _ = ω ^ 2 := by rw [hω3, one_pow, one_mul]

private lemma k328r6f_omega_sq8 (F : Type) [Field F] (ω : F) (hω3 : ω ^ 3 = 1) :
    (ω ^ 2) ^ 8 = ω := by
  calc (ω ^ 2) ^ 8 = (ω ^ 3) ^ 5 * ω := by ring
    _ = ω := by rw [hω3, one_pow, one_mul]

private def k328r6f_Pm (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1]

private def k328r6f_Pinv (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1]

private lemma k328r6f_Pm_mul_Pinv (F : Type) [Field F] :
    k328r6f_Pm F * k328r6f_Pinv F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k328r6f_Pm, k328r6f_Pinv, Matrix.mul_apply, Fin.sum_univ_four]

private lemma k328r6f_Pinv_mul_Pm (F : Type) [Field F] :
    k328r6f_Pinv F * k328r6f_Pm F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k328r6f_Pm, k328r6f_Pinv, Matrix.mul_apply, Fin.sum_univ_four]

private def k328r6f_P (F : Type) [Field F] : GL (Fin 4) F :=
  ⟨k328r6f_Pm F, k328r6f_Pinv F, k328r6f_Pm_mul_Pinv F, k328r6f_Pinv_mul_Pm F⟩

private def k328r6f_Tm (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private lemma k328r6f_Tm_mul_Tm (F : Type) [Field F] : k328r6f_Tm F * k328r6f_Tm F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k328r6f_Tm, Matrix.mul_apply, Fin.sum_univ_four]

private def k328r6f_T (F : Type) [Field F] : GL (Fin 4) F :=
  ⟨k328r6f_Tm F, k328r6f_Tm F, k328r6f_Tm_mul_Tm F, k328r6f_Tm_mul_Tm F⟩

private def k328r6f_Dz (F : Type) [Field F] (ω : F) (hω3 : ω ^ 3 = 1) : GL (Fin 4) F where
  val := Matrix.diagonal ![1, ω ^ 2, ω, 1]
  inv := Matrix.diagonal ![1, ω, ω ^ 2, 1]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    apply congrArg Matrix.diagonal
    funext i
    fin_cases i <;>
      simp [k328r6f_omega_mul_sq F ω hω3, k328r6f_sq_mul_omega F ω hω3]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    apply congrArg Matrix.diagonal
    funext i
    fin_cases i <;>
      simp [k328r6f_omega_mul_sq F ω hω3, k328r6f_sq_mul_omega F ω hω3]

private def k328r6f_Dt (F : Type) [Field F] (ω : F) (hω3 : ω ^ 3 = 1) : GL (Fin 4) F where
  val := Matrix.diagonal ![1, ω, ω ^ 2, 1]
  inv := Matrix.diagonal ![1, ω ^ 2, ω, 1]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    apply congrArg Matrix.diagonal
    funext i
    fin_cases i <;>
      simp [k328r6f_omega_mul_sq F ω hω3, k328r6f_sq_mul_omega F ω hω3]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    apply congrArg Matrix.diagonal
    funext i
    fin_cases i <;>
      simp [k328r6f_omega_mul_sq F ω hω3, k328r6f_sq_mul_omega F ω hω3]

private lemma k328r6f_mem_statedSU_of {F : Type} [Field F] {A : GL (Fin 4) F}
    (hdet : (A : Matrix (Fin 4) (Fin 4) F).det = 1)
    (huni : ((A : Matrix (Fin 4) (Fin 4) F).map (fun x => x ^ 8))ᵀ *
      (A : Matrix (Fin 4) (Fin 4) F) = 1) :
    A ∈ StatedSU 4 8 F :=
  Subgroup.subset_closure ⟨hdet, huni⟩

private lemma k328r6f_P_det (F : Type) [Field F] :
    (k328r6f_P F : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  have h : (k328r6f_P F : Matrix (Fin 4) (Fin 4) F) =
      ((Equiv.swap (1 : Fin 4) 2) * (Equiv.swap (0 : Fin 4) 1)).permMatrix F := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [k328r6f_P, k328r6f_Pm, Equiv.Perm.permMatrix, Equiv.swap_apply_def,
        Equiv.Perm.mul_apply]
  rw [h, Matrix.det_permutation, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (by decide : (1 : Fin 4) ≠ 2),
    Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 1)]
  norm_num

private lemma k328r6f_T_det (F : Type) [Field F] [CharP F 2] :
    (k328r6f_T F : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  have h : (k328r6f_T F : Matrix (Fin 4) (Fin 4) F) =
      (Equiv.swap (0 : Fin 4) 1).permMatrix F := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [k328r6f_T, k328r6f_Tm, Equiv.Perm.permMatrix, Equiv.swap_apply_def]
  rw [h, Matrix.det_permutation, Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 1)]
  norm_num
  rw [CharTwo.neg_eq]

private lemma k328r6f_P_mem (F : Type) [Field F] : k328r6f_P F ∈ StatedSU 4 8 F := by
  refine k328r6f_mem_statedSU_of (k328r6f_P_det F) ?_
  have hmap : (k328r6f_P F : Matrix (Fin 4) (Fin 4) F).map (fun x => x ^ 8) =
      (k328r6f_P F : Matrix (Fin 4) (Fin 4) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [k328r6f_P, k328r6f_Pm]
  rw [hmap]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k328r6f_P, k328r6f_Pm, Matrix.mul_apply, Fin.sum_univ_four]

private lemma k328r6f_T_mem (F : Type) [Field F] [CharP F 2] :
    k328r6f_T F ∈ StatedSU 4 8 F := by
  refine k328r6f_mem_statedSU_of (k328r6f_T_det F) ?_
  have hmap : (k328r6f_T F : Matrix (Fin 4) (Fin 4) F).map (fun x => x ^ 8) =
      (k328r6f_T F : Matrix (Fin 4) (Fin 4) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [k328r6f_T, k328r6f_Tm]
  rw [hmap]
  have htr : (k328r6f_T F : Matrix (Fin 4) (Fin 4) F)ᵀ =
      (k328r6f_T F : Matrix (Fin 4) (Fin 4) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [k328r6f_T, k328r6f_Tm]
  rw [htr]
  simpa [k328r6f_T] using k328r6f_Tm_mul_Tm F

private lemma k328r6f_diag_unitary (F : Type) [Field F] (d : Fin 4 → F)
    (hd : ∀ i, d i ^ 8 * d i = 1) :
    ((Matrix.diagonal d : Matrix (Fin 4) (Fin 4) F).map (fun x => x ^ 8))ᵀ *
      Matrix.diagonal d = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_apply, Matrix.mul_apply, hd]

private lemma k328r6f_Dz_det (F : Type) [Field F] (ω : F) (hω3 : ω ^ 3 = 1) :
    (k328r6f_Dz F ω hω3 : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  show (Matrix.diagonal ![1, ω ^ 2, ω, 1] : Matrix (Fin 4) (Fin 4) F).det = 1
  rw [Matrix.det_diagonal, Fin.prod_univ_four]
  simp [k328r6f_sq_mul_omega F ω hω3]

private lemma k328r6f_Dz_unit (F : Type) [Field F] (ω : F) (hω3 : ω ^ 3 = 1) :
    ((k328r6f_Dz F ω hω3 : Matrix (Fin 4) (Fin 4) F).map (fun x => x ^ 8))ᵀ *
      (k328r6f_Dz F ω hω3 : Matrix (Fin 4) (Fin 4) F) = 1 := by
  show (((Matrix.diagonal ![1, ω ^ 2, ω, 1]) : Matrix (Fin 4) (Fin 4) F).map
      (fun x => x ^ 8))ᵀ * (Matrix.diagonal ![1, ω ^ 2, ω, 1]) = 1
  refine k328r6f_diag_unitary F (![1, ω ^ 2, ω, 1]) ?_
  intro i
  fin_cases i <;>
    simp [k328r6f_omega8 F ω hω3, k328r6f_omega_sq8 F ω hω3,
      k328r6f_omega_mul_sq F ω hω3, k328r6f_sq_mul_omega F ω hω3]

private lemma k328r6f_Dz_mem (F : Type) [Field F] (ω : F) (hω3 : ω ^ 3 = 1) :
    k328r6f_Dz F ω hω3 ∈ StatedSU 4 8 F :=
  k328r6f_mem_statedSU_of (k328r6f_Dz_det F ω hω3) (k328r6f_Dz_unit F ω hω3)

private lemma k328r6f_Dt_det (F : Type) [Field F] (ω : F) (hω3 : ω ^ 3 = 1) :
    (k328r6f_Dt F ω hω3 : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  show (Matrix.diagonal ![1, ω, ω ^ 2, 1] : Matrix (Fin 4) (Fin 4) F).det = 1
  rw [Matrix.det_diagonal, Fin.prod_univ_four]
  simp [k328r6f_omega_mul_sq F ω hω3]

private lemma k328r6f_Dt_unit (F : Type) [Field F] (ω : F) (hω3 : ω ^ 3 = 1) :
    ((k328r6f_Dt F ω hω3 : Matrix (Fin 4) (Fin 4) F).map (fun x => x ^ 8))ᵀ *
      (k328r6f_Dt F ω hω3 : Matrix (Fin 4) (Fin 4) F) = 1 := by
  show (((Matrix.diagonal ![1, ω, ω ^ 2, 1]) : Matrix (Fin 4) (Fin 4) F).map
      (fun x => x ^ 8))ᵀ * (Matrix.diagonal ![1, ω, ω ^ 2, 1]) = 1
  refine k328r6f_diag_unitary F (![1, ω, ω ^ 2, 1]) ?_
  intro i
  fin_cases i <;>
    simp [k328r6f_omega8 F ω hω3, k328r6f_omega_sq8 F ω hω3,
      k328r6f_omega_mul_sq F ω hω3, k328r6f_sq_mul_omega F ω hω3]

private lemma k328r6f_Dt_mem (F : Type) [Field F] (ω : F) (hω3 : ω ^ 3 = 1) :
    k328r6f_Dt F ω hω3 ∈ StatedSU 4 8 F :=
  k328r6f_mem_statedSU_of (k328r6f_Dt_det F ω hω3) (k328r6f_Dt_unit F ω hω3)

private lemma k328r6f_P_cent (F : Type) [Field F] (ω : F) (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1]) :
    z₀ * k328r6f_P F = k328r6f_P F * z₀ := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k328r6f_P, k328r6f_Pm, hz, Matrix.mul_apply, Fin.sum_univ_four]

private lemma k328r6f_T_cent (F : Type) [Field F] (ω : F) (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1]) :
    z₀ * k328r6f_T F = k328r6f_T F * z₀ := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k328r6f_T, k328r6f_Tm, hz, Matrix.mul_apply, Fin.sum_univ_four]

private lemma k328r6f_Dz_cent (F : Type) [Field F] (ω : F) (hω3 : ω ^ 3 = 1)
    (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1]) :
    z₀ * k328r6f_Dz F ω hω3 = k328r6f_Dz F ω hω3 * z₀ := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k328r6f_Dz, hz, Matrix.mul_apply, Fin.sum_univ_four] ; ring

private lemma k328r6f_Dt_cent (F : Type) [Field F] (ω : F) (hω3 : ω ^ 3 = 1)
    (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1]) :
    z₀ * k328r6f_Dt F ω hω3 = k328r6f_Dt F ω hω3 * z₀ := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k328r6f_Dt, hz, Matrix.mul_apply, Fin.sum_univ_four] ; ring

private lemma k328r6f_comm_z (F : Type) [Field F] (ω : F) (hω3 : ω ^ 3 = 1)
    (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1]) :
    k328r6f_P F * k328r6f_Dz F ω hω3 = z₀ * k328r6f_Dz F ω hω3 * k328r6f_P F := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k328r6f_P, k328r6f_Pm, k328r6f_Dz, hz, Matrix.mul_apply, Fin.sum_univ_four,
      k328r6f_omega_mul_sq F ω hω3] ; ring

private lemma k328r6f_comm_t (F : Type) [Field F] (ω : F) (hω3 : ω ^ 3 = 1)
    (t₀ : GL (Fin 4) F)
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    k328r6f_T F * k328r6f_Dt F ω hω3 = t₀ * k328r6f_Dt F ω hω3 * k328r6f_T F := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k328r6f_T, k328r6f_Tm, k328r6f_Dt, ht, Matrix.mul_apply, Fin.sum_univ_four,
      k328r6f_sq_mul_omega F ω hω3]

private lemma k328r6f_z_mem_stdComp (F : Type) [Field F] (ω : F)
    (hω : ω ^ 2 + ω + 1 = 0) (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1]) :
    z₀ ∈ stdComp (StatedSU 4 8 F) z₀ := by
  have hω3 : ω ^ 3 = 1 := k328r6f_omega_cube F ω hω
  have hP : k328r6f_P F ∈ StatedSU 4 8 F ⊓ Subgroup.centralizer {z₀} :=
    ⟨k328r6f_P_mem F, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact k328r6f_P_cent F ω z₀ hz⟩
  have hD : k328r6f_Dz F ω hω3 ∈ StatedSU 4 8 F ⊓ Subgroup.centralizer {z₀} :=
    ⟨k328r6f_Dz_mem F ω hω3, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact k328r6f_Dz_cent F ω hω3 z₀ hz⟩
  have hz_eq : ⁅k328r6f_P F, k328r6f_Dz F ω hω3⁆ = z₀ := by
    rw [commutatorElement_def, k328r6f_comm_z F ω hω3 z₀ hz]
    group
  rw [stdComp]
  have hmem := Subgroup.commutator_mem_commutator hP hD
  rw [hz_eq] at hmem
  exact hmem

private lemma k328r6f_t_mem_stdComp (F : Type) [Field F] [Fintype F]
    (hF : Fintype.card F = 64) (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (z₀ t₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    t₀ ∈ stdComp (StatedSU 4 8 F) z₀ := by
  have hchar : CharP F 2 := k328r6f_charP F hF
  have hω3 : ω ^ 3 = 1 := k328r6f_omega_cube F ω hω
  have hT : k328r6f_T F ∈ StatedSU 4 8 F ⊓ Subgroup.centralizer {z₀} :=
    ⟨k328r6f_T_mem F, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact k328r6f_T_cent F ω z₀ hz⟩
  have hD : k328r6f_Dt F ω hω3 ∈ StatedSU 4 8 F ⊓ Subgroup.centralizer {z₀} :=
    ⟨k328r6f_Dt_mem F ω hω3, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact k328r6f_Dt_cent F ω hω3 z₀ hz⟩
  have ht_eq : ⁅k328r6f_T F, k328r6f_Dt F ω hω3⁆ = t₀ := by
    rw [commutatorElement_def, k328r6f_comm_t F ω hω3 t₀ ht]
    group
  rw [stdComp]
  have hmem := Subgroup.commutator_mem_commutator hT hD
  rw [ht_eq] at hmem
  exact hmem

private lemma k328r6f_z_pow3 (F : Type) [Field F] (ω : F) (hω3 : ω ^ 3 = 1)
    (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1]) :
    z₀ ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hz, Matrix.diagonal_pow]
  rw [show (![ω, ω, ω, 1] : Fin 4 → F) ^ 3 = 1 by
    funext i
    fin_cases i <;> simp [hω3]]
  simp

private lemma k328r6f_z_ne_one (F : Type) [Field F] [Fintype F]
    (hF : Fintype.card F = 64) (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1]) :
    z₀ ≠ 1 := by
  intro h
  have hω1 : ω = 1 := by
    have h00 : (z₀ : Matrix (Fin 4) (Fin 4) F) 0 0 = (1 : Matrix (Fin 4) (Fin 4) F) 0 0 := by
      simp [h]
    rw [hz] at h00
    simpa using h00
  exact k328r6f_omega_ne_one F hF ω hω hω1

private lemma k328r6f_orderOf_z (F : Type) [Field F] [Fintype F]
    (hF : Fintype.card F = 64) (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (z₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1]) :
    orderOf z₀ = 3 := by
  have hω3 : ω ^ 3 = 1 := k328r6f_omega_cube F ω hω
  exact orderOf_eq_prime (k328r6f_z_pow3 F ω hω3 z₀ hz) (k328r6f_z_ne_one F hF ω hω z₀ hz)

private lemma k328r6f_t_pow3 (F : Type) [Field F] (ω : F) (hω3 : ω ^ 3 = 1)
    (t₀ : GL (Fin 4) F)
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    t₀ ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, ht, Matrix.diagonal_pow]
  rw [show (![ω, ω ^ 2, 1, 1] : Fin 4 → F) ^ 3 = 1 by
    funext i
    fin_cases i <;> simp [hω3, k328r6f_omega_sq_cube F ω hω3]]
  simp

private lemma k328r6f_t_ne_one (F : Type) [Field F] [Fintype F]
    (hF : Fintype.card F = 64) (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (t₀ : GL (Fin 4) F)
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    t₀ ≠ 1 := by
  intro h
  have hω1 : ω = 1 := by
    have h00 : (t₀ : Matrix (Fin 4) (Fin 4) F) 0 0 = (1 : Matrix (Fin 4) (Fin 4) F) 0 0 := by
      simp [h]
    rw [ht] at h00
    simpa using h00
  exact k328r6f_omega_ne_one F hF ω hω hω1

private lemma k328r6f_orderOf_t (F : Type) [Field F] [Fintype F]
    (hF : Fintype.card F = 64) (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (t₀ : GL (Fin 4) F)
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    orderOf t₀ = 3 := by
  have hω3 : ω ^ 3 = 1 := k328r6f_omega_cube F ω hω
  exact orderOf_eq_prime (k328r6f_t_pow3 F ω hω3 t₀ ht) (k328r6f_t_ne_one F hF ω hω t₀ ht)

private lemma k328r6f_commute (F : Type) [Field F] (ω : F)
    (z₀ t₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    z₀ * t₀ = t₀ * z₀ := by
  apply Units.ext
  change (z₀ : Matrix (Fin 4) (Fin 4) F) * (t₀ : Matrix (Fin 4) (Fin 4) F) =
    (t₀ : Matrix (Fin 4) (Fin 4) F) * (z₀ : Matrix (Fin 4) (Fin 4) F)
  rw [hz, ht, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  exact mul_comm _ _

private lemma k328r6f_not_zpowers (F : Type) [Field F] [Fintype F]
    (hF : Fintype.card F = 64) (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (z₀ t₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    t₀ ∉ Subgroup.zpowers z₀ := by
  have hzord : orderOf z₀ = 3 := k328r6f_orderOf_z F hF ω hω z₀ hz
  have ht00 : (t₀ : Matrix (Fin 4) (Fin 4) F) 0 0 = ω := by rw [ht]; simp
  have ht11 : (t₀ : Matrix (Fin 4) (Fin 4) F) 1 1 = ω ^ 2 := by rw [ht]; simp
  have htne : (t₀ : Matrix (Fin 4) (Fin 4) F) 0 0 ≠ (t₀ : Matrix (Fin 4) (Fin 4) F) 1 1 := by
    rw [ht00, ht11]
    exact k328r6f_omega_ne_sq F hF ω hω
  intro ht_mem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ht_mem
  have hmod : z₀ ^ (k % (3 : ℤ)) = t₀ := by
    rw [show (3 : ℤ) = (orderOf z₀ : ℤ) by rw [hzord]; norm_num, zpow_mod_orderOf, hk]
  have hkm : k % (3 : ℤ) = 0 ∨ k % (3 : ℤ) = 1 ∨ k % (3 : ℤ) = 2 := by omega
  rcases hkm with h0 | h1 | h2
  · apply htne
    rw [← hmod, h0]
    simp
  · apply htne
    rw [← hmod, h1, zpow_one, hz]
    simp
  · apply htne
    rw [← hmod, h2, zpow_ofNat, Units.val_pow_eq_pow_val, hz, Matrix.diagonal_pow]
    simp

theorem row6_facts (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 64) (ω : F)
    (hω : ω ^ 2 + ω + 1 = 0) (z₀ t₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    FactsLeaf (StatedSU 4 8 F) z₀ t₀ := by
  have hzcomp : z₀ ∈ stdComp (StatedSU 4 8 F) z₀ :=
    k328r6f_z_mem_stdComp F ω hω z₀ hz
  have htcomp : t₀ ∈ stdComp (StatedSU 4 8 F) z₀ :=
    k328r6f_t_mem_stdComp F hF ω hω z₀ t₀ hz ht
  refine ⟨stdComp_le (StatedSU 4 8 F) z₀ hzcomp, hzcomp, htcomp,
    k328r6f_orderOf_z F hF ω hω z₀ hz,
    k328r6f_orderOf_t F hF ω hω t₀ ht,
    k328r6f_commute F ω z₀ t₀ hz ht,
    k328r6f_not_zpowers F hF ω hω z₀ t₀ hz ht⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
