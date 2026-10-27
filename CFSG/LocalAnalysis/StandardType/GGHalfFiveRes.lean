module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveF4

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

@[expose] noncomputable def resBlocks (n : ℕ) :
    Matrix (Fin n) (Fin n) (Matrix (Fin 2) (Fin 2) F2) →+*
      Matrix (Fin (n * 2)) (Fin (n * 2)) F2 :=
  ((Matrix.reindexRingEquiv F2 (finProdFinEquiv : Fin n × Fin 2 ≃ Fin (n * 2))).toRingHom).comp
    (Matrix.compRingEquiv (Fin n) (Fin 2) F2).toRingHom

theorem resBlocks_apply (n : ℕ) (B : Matrix (Fin n) (Fin n) (Matrix (Fin 2) (Fin 2) F2))
    (i i' : Fin n) (j j' : Fin 2) :
    resBlocks n B (finProdFinEquiv (i, j)) (finProdFinEquiv (i', j')) = B i i' j j' := by
  change (Matrix.reindex (finProdFinEquiv : Fin n × Fin 2 ≃ Fin (n * 2))
      (finProdFinEquiv : Fin n × Fin 2 ≃ Fin (n * 2))
      ((Matrix.comp (Fin n) (Fin n) (Fin 2) (Fin 2) F2) B))
      (finProdFinEquiv (i, j)) (finProdFinEquiv (i', j')) = B i i' j j'
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.comp_apply]
  simp [Equiv.symm_apply_apply]

theorem resBlocks_injective (n : ℕ) : Function.Injective (resBlocks n) := by
  intro B C h
  exact (Matrix.compRingEquiv (Fin n) (Fin 2) F2).injective
    ((Matrix.reindexRingEquiv F2 (finProdFinEquiv : Fin n × Fin 2 ≃ Fin (n * 2))).injective h)

@[expose] noncomputable def resMat (n : ℕ) :
    Matrix (Fin n) (Fin n) F4 →+* Matrix (Fin (n * 2)) (Fin (n * 2)) F2 :=
  (resBlocks n).comp f4Eps.mapMatrix

theorem resMat_apply (n : ℕ) (A : Matrix (Fin n) (Fin n) F4) (i i' : Fin n) (j j' : Fin 2) :
    resMat n A (finProdFinEquiv (i, j)) (finProdFinEquiv (i', j')) = f4Eps (A i i') j j' := by
  rw [resMat, RingHom.comp_apply, RingHom.mapMatrix_apply, resBlocks_apply, Matrix.map_apply]

theorem resMat_injective (n : ℕ) : Function.Injective (resMat n) := by
  intro A B h
  have h1 : f4Eps.mapMatrix A = f4Eps.mapMatrix B := resBlocks_injective n h
  exact Matrix.map_injective (RingHom.injective f4Eps)
    (by simpa only [RingHom.mapMatrix_apply] using h1)

theorem resMat_transpose (n : ℕ) (A : Matrix (Fin n) (Fin n) F4) :
    (resMat n A).transpose = resMat n A.transpose := by
  ext r s
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective r
  obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective s
  rw [Matrix.transpose_apply, resMat_apply, resMat_apply, Matrix.transpose_apply]
  have h := congrFun (congrFun (f4Eps_transpose (A i' i)) j') j
  simp only [Matrix.transpose_apply] at h
  exact h.symm

theorem det_resMat_of_isUnit (n : ℕ) {A : Matrix (Fin n) (Fin n) F4} (hA : IsUnit A.det) :
    (resMat n A).det = 1 := by
  have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have hmap : resMat n A * resMat n A⁻¹ = 1 := by
    rw [← map_mul, hmul, map_one]
  have hdet : (resMat n A).det * (resMat n A⁻¹).det = 1 := by
    rw [← Matrix.det_mul, hmap, Matrix.det_one]
  have hne : (resMat n A).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet
    exact zero_ne_one hdet
  have hcard : Nat.card F2 = 2 := by
    have := GaloisField.card 2 1 (by omega)
    simpa using this
  have h01 : ∀ z : F2, z = 0 ∨ z = 1 := by
    intro z
    by_cases hz : z = 0
    · exact Or.inl hz
    · obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F2)).mp hcard
      exact Or.inr ((huniq z hz).trans (huniq 1 one_ne_zero).symm)
  rcases h01 ((resMat n A).det) with h | h
  · exact absurd h hne
  · exact h

@[expose] noncomputable def resGL (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin n) F4 →* SpecialLinearGroup (Fin (n * 2)) F2 where
  toFun g := ⟨resMat n (g : Matrix (Fin n) (Fin n) F4),
    det_resMat_of_isUnit n ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := by
    apply Subtype.ext
    change resMat n ((g * h : Matrix.GeneralLinearGroup (Fin n) F4) : Matrix (Fin n) (Fin n) F4) =
      resMat n (g : Matrix (Fin n) (Fin n) F4) * resMat n (h : Matrix (Fin n) (Fin n) F4)
    rw [Units.val_mul, map_mul]

@[expose] noncomputable def resSL (n : ℕ) :
    SpecialLinearGroup (Fin n) F4 →* SpecialLinearGroup (Fin (n * 2)) F2 :=
  (resGL n).comp SpecialLinearGroup.toGL

theorem coe_resGL (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) F4) :
    ((resGL n g : SpecialLinearGroup (Fin (n * 2)) F2) : Matrix (Fin (n * 2)) (Fin (n * 2)) F2) =
      resMat n (g : Matrix (Fin n) (Fin n) F4) := rfl

theorem coe_resSL (n : ℕ) (A : SpecialLinearGroup (Fin n) F4) :
    ((resSL n A : SpecialLinearGroup (Fin (n * 2)) F2) : Matrix (Fin (n * 2)) (Fin (n * 2)) F2) =
      resMat n (A : Matrix (Fin n) (Fin n) F4) := rfl

theorem resGL_injective (n : ℕ) : Function.Injective (resGL n) := by
  intro g g' h
  apply Units.ext
  apply resMat_injective n
  have hval := congrArg Subtype.val h
  simpa only [coe_resGL] using hval

theorem resSL_injective (n : ℕ) : Function.Injective (resSL n) := by
  exact (resGL_injective n).comp SpecialLinearGroup.toGL_injective

@[expose] noncomputable def omegaScalar : Matrix.GeneralLinearGroup (Fin 3) F4 :=
  Units.map (Matrix.scalar (Fin 3) : F4 →+* Matrix (Fin 3) (Fin 3) F4).toMonoidHom
    (Units.mk0 f4Omega f4Omega_ne_zero)

@[expose] noncomputable def zeta5 : SpecialLinearGroup (Fin 6) F2 :=
  omegaBlock 5 0 * omegaBlock 5 2 * omegaBlock 5 4

private theorem omegaBlock_coe (n : ℕ) (k : Fin n) :
    ((omegaBlock n k : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      signedPerm (Equiv.swap k.castSucc k.succ) 1 *
        (1 + Matrix.single k.castSucc k.succ (1 : F2)) := by
  rw [omegaBlock, Matrix.SpecialLinearGroup.coe_mul, coe_weylRep_of_two n gf2_two k,
    SpecialLinearGroup.transvection_coe]

private theorem omegaBlock_apply (n : ℕ) (k : Fin n) (r s : Fin (n + 1)) :
    ((omegaBlock n k : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) r s =
      (if r = (Equiv.swap k.castSucc k.succ) s then 1 else 0) +
        (if k.succ = r ∧ k.succ = s then 1 else 0) := by
  rw [omegaBlock_coe, Matrix.mul_add, Matrix.mul_one, signedPerm_mul_single,
    Equiv.swap_apply_left]
  rw [Matrix.add_apply, signedPerm_apply, Matrix.single_apply]
  simp only [Pi.one_apply, mul_one]

private theorem omegaScalar_coe :
    (omegaScalar : Matrix (Fin 3) (Fin 3) F4) = Matrix.scalar (Fin 3) f4Omega := by
  rw [omegaScalar, Units.coe_map]
  rfl

theorem zeta5_eq : zeta5 = resGL 3 omegaScalar := by
  apply Subtype.ext
  rw [zeta5, coe_resGL, omegaScalar_coe]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext r s
  obtain ⟨⟨i, j⟩, rfl⟩ := (finProdFinEquiv (m := 3) (n := 2)).surjective r
  obtain ⟨⟨i', j'⟩, rfl⟩ := (finProdFinEquiv (m := 3) (n := 2)).surjective s
  rw [resMat_apply]
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp [Matrix.mul_apply, Fin.sum_univ_six, omegaBlock_apply,
      Matrix.scalar_apply, Matrix.diagonal_apply, f4Eps_omega, finProdFinEquiv,
      Equiv.swap_apply_def]

end CFSG.StandardType.GGHalf

end
