module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3Diag
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3Unitri

public section

open scoped Matrix

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

variable {F : Type*} [Field F]

@[expose] def natAct : Matrix.SpecialLinearGroup (Fin 3) F →* AddMonoid.End (Fin 3 → F) where
  toFun g := (Matrix.mulVecLin (g : Matrix (Fin 3) (Fin 3) F)).toAddMonoidHom
  map_one' := by
    ext v i
    simp
    rfl
  map_mul' g h := by
    ext v i
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVecLin_mul]
    rfl

@[expose] def dualAct : Matrix.SpecialLinearGroup (Fin 3) F →* AddMonoid.End (Fin 3 → F) where
  toFun g := (Matrix.mulVecLin
    ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ).toAddMonoidHom
  map_one' := by
    ext v i
    simp
    rfl
  map_mul' g h := by
    ext v i
    rw [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul,
      Matrix.mulVecLin_mul]
    rfl

theorem mulVec_diag_apply {M : Matrix (Fin 3) (Fin 3) F} (hM : ∀ i j, i ≠ j → M i j = 0)
    (v : Fin 3 → F) (i : Fin 3) : (M *ᵥ v) i = M i i * v i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · intro j _ hj
    rw [hM i j (Ne.symm hj), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem fixedFree_of_diag {M : Matrix (Fin 3) (Fin 3) F} (hM : ∀ i j, i ≠ j → M i j = 0)
    (hd : ∀ i, M i i ≠ 1) (v : Fin 3 → F) (hv : M *ᵥ v = v) : v = 0 := by
  funext i
  have h1 : M i i * v i = v i := by
    rw [← mulVec_diag_apply hM v i]
    exact congrFun hv i
  have h2 : (M i i - 1) * v i = 0 := by
    rw [sub_mul, one_mul, h1, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) (hd i)
  · exact h

theorem inv_diag_mul_apply {t : Matrix.SpecialLinearGroup (Fin 3) F} (ht : IsDiagSL t)
    (i : Fin 3) :
    ((t⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i *
      (t : Matrix (Fin 3) (Fin 3) F) i i = 1 := by
  have h : ((t⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (t : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hinv : ∀ i j : Fin 3, i ≠ j →
      ((t⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j = 0 :=
    isDiagSL_inv ht
  have h2 := congrFun (congrFun h i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h2
  · simpa [Matrix.one_apply] using h2
  · intro k _ hk
    rw [hinv i k (Ne.symm hk), zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem fixedFree_dual {t : Matrix.SpecialLinearGroup (Fin 3) F} (ht : IsDiagSL t)
    (hd : ∀ i, (t : Matrix (Fin 3) (Fin 3) F) i i ≠ 1) (v : Fin 3 → F)
    (hv : ((t⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v = v) :
    v = 0 := by
  refine fixedFree_of_diag ?_ ?_ v hv
  · intro i j hij
    rw [Matrix.transpose_apply]
    exact isDiagSL_inv ht j i (Ne.symm hij)
  · intro i h1
    rw [Matrix.transpose_apply] at h1
    apply hd i
    have h2 := inv_diag_mul_apply ht i
    rw [h1, one_mul] at h2
    exact h2

def diagMk (x y z : F) (h : x * y * z = 1) : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨Matrix.diagonal ![x, y, z], by simpa [Matrix.det_diagonal, Fin.prod_univ_three] using h⟩

theorem diagMk_isDiag (x y z : F) (h : x * y * z = 1) : IsDiagSL (diagMk x y z h) := by
  intro i j hij
  simp [diagMk, Matrix.diagonal_apply_ne _ hij]

theorem diagMk_mem (x y z : F) (h : x * y * z = 1) :
    diagMk x y z h ∈ diagSL (F := F) :=
  diagMk_isDiag x y z h

theorem diagMk_ne_one (x y z : F) (h : x * y * z = 1) (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1) :
    ∀ i, (diagMk x y z h : Matrix (Fin 3) (Fin 3) F) i i ≠ 1 := by
  intro i
  fin_cases i <;> simp [diagMk, hx, hy, hz]

theorem diagMk_comm_fst (x y z : F) (h : x * y * z = 1) (hxy : x = y) (a : F) :
    diagMk x y z h * unitriMk a 0 0 = unitriMk a 0 0 * diagMk x y z h := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagMk, unitriMk, unitriMat, Matrix.mul_apply, Fin.sum_univ_three, hxy] <;> ring

theorem diagMk_comm_snd (x y z : F) (h : x * y * z = 1) (hyz : y = z) (b : F) :
    diagMk x y z h * unitriMk 0 b 0 = unitriMk 0 b 0 * diagMk x y z h := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagMk, unitriMk, unitriMat, Matrix.mul_apply, Fin.sum_univ_three, hyz] <;> ring

theorem diagMk_comm_thd (x y z : F) (h : x * y * z = 1) (hxz : x = z) (c : F) :
    diagMk x y z h * unitriMk 0 0 c = unitriMk 0 0 c * diagMk x y z h := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagMk, unitriMk, unitriMat, Matrix.mul_apply, Fin.sum_univ_three, hxz] <;> ring

theorem unitriMk_factor (a b c : F) :
    unitriMk a b c = unitriMk a 0 0 * unitriMk 0 b 0 * unitriMk 0 0 (c - a * b) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitriMk, unitriMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem eq_unitriMk_of_isUnitri {u : Matrix.SpecialLinearGroup (Fin 3) F} (hu : IsUnitri u) :
    u = unitriMk ((u : Matrix (Fin 3) (Fin 3) F) 0 1) ((u : Matrix (Fin 3) (Fin 3) F) 1 2)
      ((u : Matrix (Fin 3) (Fin 3) F) 0 2) := by
  obtain ⟨g10, g20, g21, g00, g11, g22⟩ := hu
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [unitriMk, unitriMat, g10, g20, g21, g00, g11, g22]

theorem eq_one_of_mul_self_eq_one [CharP F 2] {τ : F} (h : τ * τ = 1) : τ = 1 := by
  have e : (τ - 1) * (τ - 1) = τ * τ - 2 * τ + 1 := by ring
  have h0 : (τ - 1) * (τ - 1) = 0 := by
    rw [e, h, CharTwo.two_eq_zero, zero_mul, sub_zero, one_add_one_eq_two, CharTwo.two_eq_zero]
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h0)

theorem torus_ne_one [CharP F 2] {τ : F} (h0 : τ ≠ 0) (h1 : τ ≠ 1) :
    (τ * τ)⁻¹ ≠ 1 := by
  intro h
  apply h1
  apply eq_one_of_mul_self_eq_one
  have hne : τ * τ ≠ 0 := mul_ne_zero h0 h0
  calc τ * τ = τ * τ * (τ * τ)⁻¹ := by rw [h, mul_one]
    _ = 1 := mul_inv_cancel₀ hne

theorem exists_tau [Fintype F] (hF : 4 ≤ Fintype.card F) : ∃ τ : F, τ ≠ 0 ∧ τ ≠ 1 := by
  classical
  by_contra hcon
  have hcon' : ∀ τ : F, τ ≠ 0 → τ = 1 := fun τ h0 => by
    by_contra h1
    exact hcon ⟨τ, h0, h1⟩
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
    intro τ _
    by_cases h : τ = 0
    · simp [h]
    · simp [hcon' τ h]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ] at h1
  have h2 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
  omega

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3
