module

public import CFSG.RankThree.SubgroupLists.SymplecticTransvections

public section

namespace CFSG.RankThree.PartOne.SEITZ4

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists

variable {r : ℕ} {K : Type} [Field K]

theorem dotProduct_spGram (x y : Fin r ⊕ Fin r → K) :
    (spGram r K *ᵥ y) ⬝ᵥ x = spForm r K x y := by
  rw [dotProduct_comm, ← spForm_eq_dotProduct]

@[expose] noncomputable def planeMat (v w : Fin r ⊕ Fin r → K) (M : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  1 + vecMulVec v ((M 0 0 + 1) • (spGram r K *ᵥ w) + M 0 1 • (spGram r K *ᵥ v)) +
    vecMulVec w (M 1 0 • (spGram r K *ᵥ w) + (M 1 1 + 1) • (spGram r K *ᵥ v))

theorem planeMat_mulVec (v w : Fin r ⊕ Fin r → K) (M : Matrix (Fin 2) (Fin 2) K)
    (x : Fin r ⊕ Fin r → K) :
    planeMat v w M *ᵥ x = x + ((M 0 0 + 1) * spForm r K x w + M 0 1 * spForm r K x v) • v +
      (M 1 0 * spForm r K x w + (M 1 1 + 1) * spForm r K x v) • w := by
  rw [planeMat, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec,
    vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul, add_dotProduct, add_dotProduct,
    smul_dotProduct, smul_dotProduct, smul_dotProduct, smul_dotProduct, dotProduct_spGram,
    dotProduct_spGram, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]

section Char2

variable [CharP K 2] {v w : Fin r ⊕ Fin r → K}

theorem spForm_wv (hvw : spForm r K v w = 1) : spForm r K w v = 1 := by
  rw [← LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt, hvw, CharTwo.neg_eq]

theorem planeMat_one : planeMat v w 1 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  simp only [Matrix.toLin'_apply, planeMat_mulVec, Matrix.one_apply_eq, Matrix.one_apply_ne,
    ne_eq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_mulVec]
  have h : (1 : K) + 1 = 0 := by simpa [one_add_one_eq_two] using h2
  simp [h]

theorem planeMat_mul (hvw : spForm r K v w = 1) (M N : Matrix (Fin 2) (Fin 2) K) :
    planeMat v w M * planeMat v w N = planeMat v w (M * N) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hwv := spForm_wv hvw
  have hvv : spForm r K v v = 0 := spForm_self v
  have hww : spForm r K w w = 0 := spForm_self w
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, planeMat_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hvv, hww,
    hvw, hwv, Matrix.mul_apply, Fin.sum_univ_two]
  match_scalars
  · ring
  · linear_combination
      (spForm r K x w * (M 0 0 + N 0 0 + 1) + spForm r K x v * (M 0 1 + N 0 1)) * h2
  · linear_combination
      (spForm r K x w * (M 1 0 + N 1 0) + spForm r K x v * (M 1 1 + N 1 1 + 1)) * h2

theorem spForm_comm' (x y : Fin r ⊕ Fin r → K) : spForm r K x y = spForm r K y x := by
  rw [← LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt, CharTwo.neg_eq]

theorem planeMat_symplectic (hvw : spForm r K v w = 1) (M : Matrix (Fin 2) (Fin 2) K)
    (hM : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1) (x y : Fin r ⊕ Fin r → K) :
    spForm r K (planeMat v w M *ᵥ x) (planeMat v w M *ᵥ y) = spForm r K x y := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hwv := spForm_wv hvw
  have hvv : spForm r K v v = 0 := spForm_self v
  have hww : spForm r K w w = 0 := spForm_self w
  simp only [planeMat_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hvv, hww,
    hvw, hwv, spForm_comm' v y, spForm_comm' w y]
  linear_combination (spForm r K x w * spForm r K y v + spForm r K x v * spForm r K y w) * hM +
    (M 0 0 * spForm r K x w * spForm r K y v + M 0 0 * M 1 0 * spForm r K x w * spForm r K y w +
      M 0 0 * spForm r K x v * spForm r K y w + M 0 1 * M 1 0 * spForm r K x w * spForm r K y v +
      2 * spForm r K x w * spForm r K y v + M 1 1 * spForm r K x w * spForm r K y v +
      2 * M 1 0 * spForm r K x w * spForm r K y w + 2 * M 0 1 * spForm r K x v * spForm r K y v +
      M 0 1 * M 1 1 * spForm r K x v * spForm r K y v +
      M 0 1 * M 1 0 * spForm r K x v * spForm r K y w +
      M 1 1 * spForm r K x v * spForm r K y w + 2 * spForm r K x v * spForm r K y w) * h2

@[expose] noncomputable def planeGL (hvw : spForm r K v w = 1)
    (M : Matrix.SpecialLinearGroup (Fin 2) K) : GL (Fin r ⊕ Fin r) K where
  val := planeMat v w (M : Matrix (Fin 2) (Fin 2) K)
  inv := planeMat v w ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  val_inv := by
    rw [planeMat_mul hvw, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, planeMat_one]
  inv_val := by
    rw [planeMat_mul hvw, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, planeMat_one]

theorem coe_planeGL (hvw : spForm r K v w = 1) (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((planeGL hvw M : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      planeMat v w (M : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem planeGL_mem (hvw : spForm r K v w = 1) (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    planeGL hvw M ∈ StatedSp r K := by
  rw [mem_statedSp_iff_preserves]
  intro x y
  rw [coe_planeGL]
  exact planeMat_symplectic hvw _ (by
    have h := M.2
    rwa [Matrix.det_fin_two] at h) x y

@[expose] noncomputable def planeHom (hvw : spForm r K v w = 1) :
    Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp r K where
  toFun M := ⟨planeGL hvw M, planeGL_mem hvw M⟩
  map_one' := Subtype.ext (Units.ext (by
    rw [coe_planeGL, Matrix.SpecialLinearGroup.coe_one, planeMat_one]; rfl))
  map_mul' M N := Subtype.ext (Units.ext (by
    change planeMat v w ((M * N : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = planeMat v w M * planeMat v w N
    rw [Matrix.SpecialLinearGroup.coe_mul, planeMat_mul hvw]))

theorem coe_planeHom (hvw : spForm r K v w = 1) (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    (((planeHom hvw M : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = planeMat v w (M : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem planeMat_upper (c : K) : planeMat v w !![1, c; 0, 1] = spTransMat v c := by
  have h : (1 : K) + 1 = 0 := by
    simpa [one_add_one_eq_two] using (CharTwo.two_eq_zero : (2 : K) = 0)
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  simp [Matrix.toLin'_apply, planeMat_mulVec, spTransMat_mulVec, h]

theorem planeMat_lower (c : K) : planeMat v w !![1, 0; c, 1] = spTransMat w c := by
  have h : (1 : K) + 1 = 0 := by
    simpa [one_add_one_eq_two] using (CharTwo.two_eq_zero : (2 : K) = 0)
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  simp [Matrix.toLin'_apply, planeMat_mulVec, spTransMat_mulVec, h]

theorem planeHom_upper (hvw : spForm r K v w = 1) (M : Matrix.SpecialLinearGroup (Fin 2) K) (c : K)
    (hM : (M : Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1]) :
    ((planeHom hvw M : StatedSp r K) : GL (Fin r ⊕ Fin r) K) = spTrans v c :=
  Units.ext (by rw [coe_planeHom, hM, planeMat_upper]; rfl)

theorem planeHom_lower (hvw : spForm r K v w = 1) (M : Matrix.SpecialLinearGroup (Fin 2) K) (c : K)
    (hM : (M : Matrix (Fin 2) (Fin 2) K) = !![1, 0; c, 1]) :
    ((planeHom hvw M : StatedSp r K) : GL (Fin r ⊕ Fin r) K) = spTrans w c :=
  Units.ext (by rw [coe_planeHom, hM, planeMat_lower]; rfl)

end Char2

end CFSG.RankThree.PartOne.SEITZ4
