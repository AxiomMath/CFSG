module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Torus
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Matrix CFSG.Open CFSG.ComponentClassification.Burgoyne.U
  CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.ClassicalEven

variable {K : Type} [Field K]

private theorem u5Syl3_bar_eq (h : UnitaryFieldData 2 2 K) (c : K) : h.bar c = c ^ 4 := by
  rw [h.bar_apply]
  norm_num

private theorem u5Syl3_card (h : UnitaryFieldData 2 2 K) : Nat.card K = 16 := by
  rw [h.card]
  norm_num

private theorem u5Syl3_exists_lam (h : UnitaryFieldData 2 2 K) :
    ∃ lam : K, lam ^ 5 = 1 ∧ lam ≠ 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite K := h.finite
  have hK : Nat.card Kˣ = 15 := by
    rw [Nat.card_units, u5Syl3_card h]
  have h5 : 5 ∣ Nat.card Kˣ := by rw [hK]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 5 h5
  refine ⟨(x : K), ?_, ?_⟩
  · have h := pow_orderOf_eq_one x
    rw [hx] at h
    simpa using congrArg (fun u : Kˣ => (u : K)) h
  · intro h1
    have hx1 : x = 1 := Units.ext h1
    rw [hx1, orderOf_one] at hx
    norm_num at hx

private theorem u5Syl3_lam_ne_zero {lam : K} (h5 : lam ^ 5 = 1) : lam ≠ 0 := by
  intro h0
  rw [h0, zero_pow (by norm_num)] at h5
  exact zero_ne_one h5

private theorem u5Syl3_lam_add_one_ne_zero {lam : K} (h2 : (2 : K) = 0) (h1 : lam ≠ 1) :
    lam + 1 ≠ 0 := by
  intro h0
  apply h1
  have h2' : (1 : K) + 1 = 0 := by rw [show (1 : K) + 1 = (2 : K) by norm_num, h2]
  have hneg : (-1 : K) = 1 := (neg_eq_iff_add_eq_zero).mpr h2'
  linear_combination h0 + hneg

private theorem u5Syl3_bar_lam {h : UnitaryFieldData 2 2 K} {lam : K} (h5 : lam ^ 5 = 1) :
    h.bar lam = lam⁻¹ := by
  rw [u5Syl3_bar_eq h]
  have h : lam ^ 4 * lam = 1 := by
    rw [← pow_succ]
    norm_num
    exact h5
  exact eq_inv_of_mul_eq_one_left h

private theorem u5Syl3_bar_root3 {h : UnitaryFieldData 2 2 K} (a : rootsOfUnity 3 K) :
    h.bar ((a : Kˣ) : K) = ((a : Kˣ) : K) := by
  have ha : ((a : Kˣ) : K) ^ 3 = 1 := by
    have h := (mem_rootsOfUnity 3 (a : Kˣ)).mp a.2
    simpa using congrArg (fun u : Kˣ => (u : K)) h
  rw [u5Syl3_bar_eq h, show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, ha, one_mul]

private def u5Syl3_G (lam : K) : Matrix (Fin 2) (Fin 2) K := !![1, 1; 1, lam]

private def u5Syl3_Gi (lam : K) : Matrix (Fin 2) (Fin 2) K :=
  (lam + 1)⁻¹ • !![lam, 1; 1, 1]

private theorem u5Syl3_G_mul_Gi {lam : K} (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0) :
    u5Syl3_G lam * u5Syl3_Gi lam = 1 := by
  have hself : ∀ x : K, x + x = 0 := fun x => by linear_combination x * h2
  have hdiag : lam * (lam + 1)⁻¹ + (lam + 1)⁻¹ = 1 := by
    rw [show lam * (lam + 1)⁻¹ + (lam + 1)⁻¹ = (lam + 1) * (lam + 1)⁻¹ by ring,
      mul_inv_cancel₀ hlam]
  have hdiag' : (lam + 1)⁻¹ + lam * (lam + 1)⁻¹ = 1 := by
    rw [add_comm]; exact hdiag
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u5Syl3_G, u5Syl3_Gi, Matrix.mul_apply, Fin.sum_univ_two, hself, hdiag, hdiag',
      mul_comm, mul_left_comm]

private theorem u5Syl3_Gi_mul_G {lam : K} (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0) :
    u5Syl3_Gi lam * u5Syl3_G lam = 1 := by
  have hself : ∀ x : K, x + x = 0 := fun x => by linear_combination x * h2
  have hdiag : lam * (lam + 1)⁻¹ + (lam + 1)⁻¹ = 1 := by
    rw [show lam * (lam + 1)⁻¹ + (lam + 1)⁻¹ = (lam + 1) * (lam + 1)⁻¹ by ring,
      mul_inv_cancel₀ hlam]
  have hdiag' : (lam + 1)⁻¹ + lam * (lam + 1)⁻¹ = 1 := by
    rw [add_comm]; exact hdiag
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u5Syl3_G, u5Syl3_Gi, Matrix.mul_apply, Fin.sum_univ_two, hself, hdiag, hdiag',
      mul_comm, mul_left_comm]

private noncomputable def u5Syl3_GL (lam : K) (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0) :
    GL (Fin 2) K :=
  ⟨u5Syl3_G lam, u5Syl3_Gi lam, u5Syl3_G_mul_Gi h2 hlam, u5Syl3_Gi_mul_G h2 hlam⟩

private theorem u5Syl3_coe_GL (lam : K) (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0) :
    ((u5Syl3_GL lam h2 hlam : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = u5Syl3_G lam := rfl

private theorem u5Syl3_coe_GL_inv (lam : K) (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0) :
    (((u5Syl3_GL lam h2 hlam)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      u5Syl3_Gi lam := rfl

private def u5Syl3_D2 : rootsOfUnity 3 K →* (Fin 2 → Kˣ) where
  toFun a := ![(a : Kˣ), (a : Kˣ)⁻¹]
  map_one' := by funext i; fin_cases i <;> simp
  map_mul' a b := by
    funext i
    fin_cases i <;> simp [mul_comm]

private noncomputable def u5Syl3_Mhom (lam : K) (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0) :
    rootsOfUnity 3 K →* GL (Fin 2) K where
  toFun a := u5Syl3_GL lam h2 hlam * torusDiag (u5Syl3_D2 a) * (u5Syl3_GL lam h2 hlam)⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul]
    group

private theorem u5Syl3_coe_Mhom (lam : K) (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0)
    (a : rootsOfUnity 3 K) :
    ((u5Syl3_Mhom lam h2 hlam a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      u5Syl3_G lam * (torusDiag (u5Syl3_D2 a) : Matrix (Fin 2) (Fin 2) K) * u5Syl3_Gi lam := by
  change (((u5Syl3_GL lam h2 hlam * torusDiag (u5Syl3_D2 a) * (u5Syl3_GL lam h2 hlam)⁻¹ :
      GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) =
    u5Syl3_G lam * (torusDiag (u5Syl3_D2 a) : Matrix (Fin 2) (Fin 2) K) * u5Syl3_Gi lam
  simp only [Units.val_mul, u5Syl3_coe_GL, u5Syl3_coe_GL_inv]

private theorem u5Syl3_det_Mhom (lam : K) (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0)
    (a : rootsOfUnity 3 K) :
    ((u5Syl3_Mhom lam h2 hlam a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  rw [u5Syl3_coe_Mhom]
  have hD : (torusDiag (u5Syl3_D2 a) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [det_torusDiag, Fin.prod_univ_two]
    simp [u5Syl3_D2]
  have hdet : (u5Syl3_Gi lam).det * (u5Syl3_G lam).det = 1 := by
    rw [← Matrix.det_mul, u5Syl3_Gi_mul_G h2 hlam, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul, hD, mul_one, mul_comm]
  exact hdet

private def u5Syl3_J (lam : K) : Matrix (Fin 2) (Fin 2) K :=
  !![0, 1 + lam; 1 + lam⁻¹, 0]

private theorem u5Syl3_G_transpose (lam : K) : (u5Syl3_G lam)ᵀ = u5Syl3_G lam := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u5Syl3_G]

private theorem u5Syl3_G_map_bar (h : UnitaryFieldData 2 2 K) {lam : K}
    (hq : h.bar lam = lam⁻¹) :
    (u5Syl3_G lam).map h.bar = u5Syl3_G lam⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u5Syl3_G, hq]

private theorem u5Syl3_G_map_bar_mul (h : UnitaryFieldData 2 2 K) {lam : K}
    (h2 : (2 : K) = 0) (hq : h.bar lam = lam⁻¹) (h0 : lam ≠ 0) :
    ((u5Syl3_G lam).map h.bar)ᵀ * u5Syl3_G lam = u5Syl3_J lam := by
  rw [← Matrix.transpose_map, u5Syl3_G_transpose, u5Syl3_G_map_bar h hq]
  have hself : ∀ x : K, x + x = 0 := fun x => by linear_combination x * h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u5Syl3_G, u5Syl3_J, Matrix.mul_apply, Fin.sum_univ_two, hself, h0, mul_comm]

private theorem u5Syl3_torusDiag_map_bar (h : UnitaryFieldData 2 2 K)
    (a : rootsOfUnity 3 K) :
    ((torusDiag (u5Syl3_D2 a) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map h.bar =
      (torusDiag (u5Syl3_D2 a) : Matrix (Fin 2) (Fin 2) K) := by
  rw [coe_torusDiag, Matrix.diagonal_map (map_zero h.bar)]
  congr 1
  funext i
  fin_cases i <;> simp [u5Syl3_D2, map_inv₀, u5Syl3_bar_root3 (h := h) a]

private theorem u5Syl3_torusDiag_mul_J_mul {lam : K} (a : rootsOfUnity 3 K) :
    (torusDiag (u5Syl3_D2 a) : Matrix (Fin 2) (Fin 2) K) * u5Syl3_J lam *
      (torusDiag (u5Syl3_D2 a) : Matrix (Fin 2) (Fin 2) K) = u5Syl3_J lam := by
  rw [coe_torusDiag]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u5Syl3_J, Matrix.mul_apply, Fin.sum_univ_two, u5Syl3_D2, mul_comm, mul_assoc]

private theorem u5Syl3_M_unitary (h : UnitaryFieldData 2 2 K) {lam : K}
    (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0) (h5 : lam ^ 5 = 1)
    (a : rootsOfUnity 3 K) :
    ((((u5Syl3_Mhom lam h2 hlam a : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ *
      ((u5Syl3_Mhom lam h2 hlam a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = 1 := by
  set G := u5Syl3_G lam
  set Gi := u5Syl3_Gi lam
  set D := (torusDiag (u5Syl3_D2 a) : Matrix (Fin 2) (Fin 2) K)
  have hGG : G * Gi = 1 := u5Syl3_G_mul_Gi h2 hlam
  have hDmap : D.map h.bar = D := u5Syl3_torusDiag_map_bar h a
  have hJ : (G.map h.bar)ᵀ * G = u5Syl3_J lam :=
    u5Syl3_G_map_bar_mul h h2 (u5Syl3_bar_lam h5) (u5Syl3_lam_ne_zero h5)
  have hDJD : D * u5Syl3_J lam * D = u5Syl3_J lam := u5Syl3_torusDiag_mul_J_mul a
  have hDtr : Dᵀ = D := by
    dsimp only [D]
    rw [coe_torusDiag]
    exact Matrix.diagonal_transpose _
  have hMmap : (G * D * Gi).map h.bar = (G.map h.bar) * D * (Gi.map h.bar) := by
    rw [Matrix.map_mul, Matrix.map_mul, hDmap]
  have hGiG : (Gi.map h.bar)ᵀ * (G.map h.bar)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hGG,
      Matrix.map_one (⇑h.bar) (map_zero h.bar) (map_one h.bar), Matrix.transpose_one]
  rw [u5Syl3_coe_Mhom]
  calc
    (((G * D * Gi).map h.bar)ᵀ * (G * D * Gi))
        = ((G.map h.bar) * D * (Gi.map h.bar))ᵀ * (G * D * Gi) := by rw [hMmap]
    _ = (Gi.map h.bar)ᵀ * Dᵀ * (G.map h.bar)ᵀ * (G * D * Gi) := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul]; noncomm_ring
    _ = (Gi.map h.bar)ᵀ * (D * ((G.map h.bar)ᵀ * G) * D) * Gi := by
          rw [hDtr]; noncomm_ring
    _ = (Gi.map h.bar)ᵀ * (D * u5Syl3_J lam * D) * Gi := by rw [hJ]
    _ = (Gi.map h.bar)ᵀ * u5Syl3_J lam * Gi := by rw [hDJD]
    _ = (Gi.map h.bar)ᵀ * ((G.map h.bar)ᵀ * G) * Gi := by rw [hJ]
    _ = ((Gi.map h.bar)ᵀ * (G.map h.bar)ᵀ) * (G * Gi) := by noncomm_ring
    _ = 1 := by rw [hGiG, hGG, one_mul]

private theorem u5Syl3_reindex_mul {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (A B : Matrix ι ι K) :
    Matrix.reindex e e (A * B) = Matrix.reindex e e A * Matrix.reindex e e B := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply]
  exact (Matrix.submatrix_mul_equiv A B e.symm e.symm e.symm).symm

private theorem u5Syl3_reindex_one {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) :
    Matrix.reindex e e (1 : Matrix ι ι K) = 1 := by
  rw [Matrix.reindex_apply, Matrix.submatrix_one_equiv]

omit [Field K] in
private theorem u5Syl3_reindex_map {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (f : K → K) (A : Matrix ι ι K) :
    (Matrix.reindex e e A).map f = Matrix.reindex e e (A.map f) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_map]

private theorem u5Syl3_det_reindex {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (A : Matrix ι ι K) :
    (Matrix.reindex e e A).det = A.det := by
  rw [Matrix.det_reindex, Equiv.self_trans_symm, Equiv.Perm.sign_refl]
  simp

private theorem u5Syl3_fromBlocks_mul_zero {m n : Type} [Fintype m] [Fintype n]
    (A A' : Matrix m m K) (D D' : Matrix n n K) :
    Matrix.fromBlocks A 0 0 D * Matrix.fromBlocks A' 0 0 D' =
      Matrix.fromBlocks (A * A') 0 0 (D * D') := by
  rw [Matrix.fromBlocks_multiply]
  simp

private noncomputable def u5Syl3_fromBlocksGL {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (A : GL m K) (D : GL n K) : GL (m ⊕ n) K where
  val := Matrix.fromBlocks (A : Matrix m m K) 0 0 (D : Matrix n n K)
  inv := Matrix.fromBlocks ((A⁻¹ : GL m K) : Matrix m m K) 0 0
    ((D⁻¹ : GL n K) : Matrix n n K)
  val_inv := by
    have hA : (A : Matrix m m K) * ((A⁻¹ : GL m K) : Matrix m m K) = 1 := by simp
    have hD : (D : Matrix n n K) * ((D⁻¹ : GL n K) : Matrix n n K) = 1 := by simp
    rw [u5Syl3_fromBlocks_mul_zero, hA, hD, Matrix.fromBlocks_one]
  inv_val := by
    have hA : ((A⁻¹ : GL m K) : Matrix m m K) * (A : Matrix m m K) = 1 := by simp
    have hD : ((D⁻¹ : GL n K) : Matrix n n K) * (D : Matrix n n K) = 1 := by simp
    rw [u5Syl3_fromBlocks_mul_zero, hA, hD, Matrix.fromBlocks_one]

private theorem u5Syl3_coe_fromBlocksGL {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (A : GL m K) (D : GL n K) :
    ((u5Syl3_fromBlocksGL A D : GL (m ⊕ n) K) : Matrix (m ⊕ n) (m ⊕ n) K) =
      Matrix.fromBlocks (A : Matrix m m K) 0 0 (D : Matrix n n K) := rfl

private theorem u5Syl3_fromBlocksGL_mul {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (A A' : GL m K) (D D' : GL n K) :
    u5Syl3_fromBlocksGL A D * u5Syl3_fromBlocksGL A' D' =
      u5Syl3_fromBlocksGL (A * A') (D * D') := by
  apply Units.ext
  rw [Units.val_mul, u5Syl3_coe_fromBlocksGL, u5Syl3_coe_fromBlocksGL, u5Syl3_coe_fromBlocksGL,
    u5Syl3_fromBlocks_mul_zero]
  simp only [Units.val_mul]

private noncomputable def u5Syl3_fromBlocksGLHom {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] : GL m K × GL n K →* GL (m ⊕ n) K where
  toFun p := u5Syl3_fromBlocksGL p.1 p.2
  map_one' := by
    apply Units.ext
    rw [u5Syl3_coe_fromBlocksGL]
    simp [Matrix.fromBlocks_one]
  map_mul' p q := (u5Syl3_fromBlocksGL_mul p.1 q.1 p.2 q.2).symm

private noncomputable def u5Syl3_glReindex {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) : GL ι K ≃* GL κ K :=
  Units.mapEquiv (RingEquiv.toMulEquiv (Matrix.reindexRingEquiv K e))

private theorem u5Syl3_coe_glReindex {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (g : GL ι K) :
    ((u5Syl3_glReindex e g : GL κ K) : Matrix κ κ K) =
      Matrix.reindex e e (g : Matrix ι ι K) := rfl

private def u5Syl3_e : ((Fin 2 ⊕ Fin 2) ⊕ Fin 1) ≃ Fin 5 :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 1))).trans finSumFinEquiv

private theorem u5Syl3_e_symm_zero : u5Syl3_e.symm 0 = Sum.inl (Sum.inl (0 : Fin 2)) := by decide
private theorem u5Syl3_e_symm_one : u5Syl3_e.symm 1 = Sum.inl (Sum.inl (1 : Fin 2)) := by decide
private theorem u5Syl3_e_symm_two : u5Syl3_e.symm 2 = Sum.inl (Sum.inr (0 : Fin 2)) := by decide
private theorem u5Syl3_e_symm_three : u5Syl3_e.symm 3 = Sum.inl (Sum.inr (1 : Fin 2)) := by decide
private theorem u5Syl3_e_symm_four : u5Syl3_e.symm 4 = Sum.inr (0 : Fin 1) := by decide

private noncomputable def u5Syl3_Bhom (lam : K) (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0) :
    rootsOfUnity 3 K × rootsOfUnity 3 K →* GL (Fin 5) K :=
  (u5Syl3_glReindex u5Syl3_e).toMonoidHom.comp <|
    u5Syl3_fromBlocksGLHom.comp <|
      MonoidHom.prod
        (u5Syl3_fromBlocksGLHom.comp
          ((u5Syl3_Mhom lam h2 hlam).prodMap (u5Syl3_Mhom lam h2 hlam)))
        (1 : rootsOfUnity 3 K × rootsOfUnity 3 K →* GL (Fin 1) K)

private noncomputable def u5Syl3_block (lam : K) (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0)
    (x : rootsOfUnity 3 K × rootsOfUnity 3 K) :
    Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin 1) ((Fin 2 ⊕ Fin 2) ⊕ Fin 1) K :=
  Matrix.fromBlocks
    (Matrix.fromBlocks ((u5Syl3_Mhom lam h2 hlam x.1 : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 0 0
      ((u5Syl3_Mhom lam h2 hlam x.2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    0 0 1

private theorem u5Syl3_coe_Bhom (lam : K) (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0)
    (x : rootsOfUnity 3 K × rootsOfUnity 3 K) :
    ((u5Syl3_Bhom lam h2 hlam x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      Matrix.reindex u5Syl3_e u5Syl3_e (u5Syl3_block lam h2 hlam x) := by
  change (((u5Syl3_glReindex u5Syl3_e
    (u5Syl3_fromBlocksGL (u5Syl3_fromBlocksGL (u5Syl3_Mhom lam h2 hlam x.1)
      (u5Syl3_Mhom lam h2 hlam x.2)) 1) : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) = _
  rw [u5Syl3_coe_glReindex, u5Syl3_coe_fromBlocksGL, u5Syl3_coe_fromBlocksGL, u5Syl3_block]
  rfl

private theorem u5Syl3_det_block (lam : K) (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0)
    (x : rootsOfUnity 3 K × rootsOfUnity 3 K) :
    (u5Syl3_block lam h2 hlam x).det = 1 := by
  rw [u5Syl3_block, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₁₂,
    u5Syl3_det_Mhom, u5Syl3_det_Mhom, Matrix.det_one, mul_one, mul_one]

private theorem u5Syl3_fromBlocks_unitary {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (f : K → K) (hf : f 0 = 0)
    (A B : Matrix m m K) (D E : Matrix n n K) :
    ((Matrix.fromBlocks A 0 0 D).map f)ᵀ * Matrix.fromBlocks B 0 0 E =
      Matrix.fromBlocks ((A.map f)ᵀ * B) 0 0 ((D.map f)ᵀ * E) := by
  rw [Matrix.fromBlocks_map, Matrix.map_zero f hf, Matrix.map_zero f hf,
    Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_zero,
    Matrix.fromBlocks_multiply]
  simp

private theorem u5Syl3_block_unitary (h : UnitaryFieldData 2 2 K) {lam : K}
    (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0) (h5 : lam ^ 5 = 1)
    (x : rootsOfUnity 3 K × rootsOfUnity 3 K) :
    ((u5Syl3_block lam h2 hlam x).map h.bar)ᵀ * u5Syl3_block lam h2 hlam x = 1 := by
  rw [u5Syl3_block, u5Syl3_fromBlocks_unitary (⇑h.bar) (map_zero h.bar)]
  rw [u5Syl3_fromBlocks_unitary (⇑h.bar) (map_zero h.bar),
    u5Syl3_M_unitary h h2 hlam h5 x.1, u5Syl3_M_unitary h h2 hlam h5 x.2,
    Matrix.map_one (⇑h.bar) (map_zero h.bar) (map_one h.bar), Matrix.transpose_one, one_mul]
  rw [Matrix.fromBlocks_one (l := Fin 2) (m := Fin 2) (α := K),
    Matrix.fromBlocks_one (l := Fin 2 ⊕ Fin 2) (m := Fin 1) (α := K)]

private theorem u5Syl3_map_pow_four (h : UnitaryFieldData 2 2 K) {ι : Type}
    (M : Matrix ι ι K) :
    M.map (fun x => x ^ 2 ^ 2) = M.map h.bar := by
  ext i j
  simp [u5Syl3_bar_eq h]

private theorem u5Syl3_Bhom_mem_SU (h : UnitaryFieldData 2 2 K) {lam : K}
    (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0) (h5 : lam ^ 5 = 1)
    (x : rootsOfUnity 3 K × rootsOfUnity 3 K) :
    u5Syl3_Bhom lam h2 hlam x ∈ StatedSU 5 (2 ^ 2) K := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [u5Syl3_coe_Bhom, u5Syl3_det_reindex, u5Syl3_det_block]
  · rw [u5Syl3_coe_Bhom, u5Syl3_reindex_map, Matrix.transpose_reindex, ← u5Syl3_reindex_mul,
      u5Syl3_map_pow_four h, u5Syl3_block_unitary h h2 hlam h5 x, u5Syl3_reindex_one]

private theorem u5Syl3_Bhom_apply (lam : K) (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0)
    (x : rootsOfUnity 3 K × rootsOfUnity 3 K) :
    u5Syl3_Bhom lam h2 hlam x =
      u5Syl3_glReindex u5Syl3_e
        (u5Syl3_fromBlocksGL (u5Syl3_fromBlocksGL (u5Syl3_Mhom lam h2 hlam x.1)
          (u5Syl3_Mhom lam h2 hlam x.2)) 1) := rfl

private theorem u5Syl3_fromBlocksGL_fst_eq_one {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] {A : GL m K} {D : GL n K}
    (h : u5Syl3_fromBlocksGL A D = 1) : A = 1 := by
  apply Units.ext
  ext i j
  have hmat : ((u5Syl3_fromBlocksGL A D : GL (m ⊕ n) K) :
      Matrix (m ⊕ n) (m ⊕ n) K) = 1 := by
    rw [h]
    rfl
  have := congrFun (congrFun hmat (Sum.inl i)) (Sum.inl j)
  simpa [u5Syl3_coe_fromBlocksGL, Matrix.fromBlocks, Matrix.one_apply] using this

private theorem u5Syl3_fromBlocksGL_snd_eq_one {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] {A : GL m K} {D : GL n K}
    (h : u5Syl3_fromBlocksGL A D = 1) : D = 1 := by
  apply Units.ext
  ext i j
  have hmat : ((u5Syl3_fromBlocksGL A D : GL (m ⊕ n) K) :
      Matrix (m ⊕ n) (m ⊕ n) K) = 1 := by
    rw [h]
    rfl
  have := congrFun (congrFun hmat (Sum.inr i)) (Sum.inr j)
  simpa [u5Syl3_coe_fromBlocksGL, Matrix.fromBlocks, Matrix.one_apply] using this

private theorem u5Syl3_Mhom_apply (lam : K) (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0)
    (a : rootsOfUnity 3 K) :
    u5Syl3_Mhom lam h2 hlam a =
      u5Syl3_GL lam h2 hlam * torusDiag (u5Syl3_D2 a) * (u5Syl3_GL lam h2 hlam)⁻¹ := rfl

private theorem u5Syl3_Mhom_eq_one_imp {lam : K} (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0)
    {a : rootsOfUnity 3 K} (h : u5Syl3_Mhom lam h2 hlam a = 1) : a = 1 := by
  have hD : torusDiag (u5Syl3_D2 a) = 1 := by
    have h' := congrArg (fun g : GL (Fin 2) K =>
      (u5Syl3_GL lam h2 hlam)⁻¹ * g * u5Syl3_GL lam h2 hlam) h
    rw [u5Syl3_Mhom_apply] at h'
    have h'' : (u5Syl3_GL lam h2 hlam)⁻¹ *
        (u5Syl3_GL lam h2 hlam * torusDiag (u5Syl3_D2 a) * (u5Syl3_GL lam h2 hlam)⁻¹) *
          u5Syl3_GL lam h2 hlam = torusDiag (u5Syl3_D2 a) := by group
    rw [h''] at h'
    simpa using h'
  have hD2 : u5Syl3_D2 a = 1 := torusDiag_injective hD
  have h0 : u5Syl3_D2 a (0 : Fin 2) = 1 := by rw [hD2]; rfl
  exact Subtype.ext (by simpa [u5Syl3_D2] using h0)

private noncomputable def u5Syl3_projB (h : UnitaryFieldData 2 2 K) {lam : K}
    (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0) (h5 : lam ^ 5 = 1) :
    rootsOfUnity 3 K × rootsOfUnity 3 K →* StatedProj (StatedSU 5 (2 ^ 2) K) :=
  (projH _).comp ((u5Syl3_Bhom lam h2 hlam).codRestrict _
    (u5Syl3_Bhom_mem_SU h h2 hlam h5))

private theorem u5Syl3_projB_eq_one_imp (h : UnitaryFieldData 2 2 K) {lam : K}
    (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0) (h5 : lam ^ 5 = 1)
    (x : rootsOfUnity 3 K × rootsOfUnity 3 K)
    (hx : u5Syl3_projB h h2 hlam h5 x = 1) : x = 1 := by
  have hx' : projH (StatedSU 5 (2 ^ 2) K)
      ((u5Syl3_Bhom lam h2 hlam).codRestrict _ (u5Syl3_Bhom_mem_SU h h2 hlam h5) x) = 1 := hx
  have hmem := (QuotientGroup.eq_one_iff _).mp hx'
  rw [Subgroup.mem_subgroupOf] at hmem
  obtain ⟨c0, hc0⟩ := hmem
  have h44 : ((u5Syl3_Bhom lam h2 hlam x : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) 4 4 = 1 := by
    rw [u5Syl3_coe_Bhom, Matrix.reindex_apply]
    simp [u5Syl3_e_symm_four, u5Syl3_block, Matrix.fromBlocks]
  have hc44 : ((u5Syl3_Bhom lam h2 hlam x : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) 4 4 = (c0 : K) := by
    have h := congrArg (fun g : GL (Fin 5) K => ((g : Matrix (Fin 5) (Fin 5) K)) 4 4)
      hc0.symm
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      MonoidHom.codRestrict_apply] using h
  have hc1 : (c0 : K) = 1 := by rw [← hc44, h44]
  have hc0u : c0 = 1 := Units.ext hc1
  have hB1 : u5Syl3_Bhom lam h2 hlam x = 1 := by
    have h : ((u5Syl3_Bhom lam h2 hlam x : GL (Fin 5) K)) =
        (GeneralLinearGroup.scalar (Fin 5) c0 : GL (Fin 5) K) := hc0.symm
    have h1 : (GeneralLinearGroup.scalar (Fin 5) (1 : Kˣ)) = (1 : GL (Fin 5) K) :=
      map_one _
    rw [hc0u, h1] at h
    exact h
  have hB2 : u5Syl3_fromBlocksGL
      (u5Syl3_fromBlocksGL (u5Syl3_Mhom lam h2 hlam x.1)
        (u5Syl3_Mhom lam h2 hlam x.2)) (1 : GL (Fin 1) K) = 1 := by
    apply (u5Syl3_glReindex u5Syl3_e).injective
    rw [u5Syl3_Bhom_apply] at hB1
    rw [hB1, map_one]
  have hinner : u5Syl3_fromBlocksGL (u5Syl3_Mhom lam h2 hlam x.1)
      (u5Syl3_Mhom lam h2 hlam x.2) = 1 :=
    u5Syl3_fromBlocksGL_fst_eq_one hB2
  have hMa : u5Syl3_Mhom lam h2 hlam x.1 = 1 := u5Syl3_fromBlocksGL_fst_eq_one hinner
  have hMb : u5Syl3_Mhom lam h2 hlam x.2 = 1 := u5Syl3_fromBlocksGL_snd_eq_one hinner
  exact Prod.ext (u5Syl3_Mhom_eq_one_imp h2 hlam hMa) (u5Syl3_Mhom_eq_one_imp h2 hlam hMb)

private theorem u5Syl3_projB_injective (h : UnitaryFieldData 2 2 K) {lam : K}
    (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0) (h5 : lam ^ 5 = 1) :
    Function.Injective (u5Syl3_projB h h2 hlam h5) := by
  intro x y hxy
  have h1 : u5Syl3_projB h h2 hlam h5 (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have h2' : x * y⁻¹ = 1 := u5Syl3_projB_eq_one_imp h h2 hlam h5 _ h1
  calc x = x * y⁻¹ * y := by group
    _ = 1 * y := by rw [h2']
    _ = y := one_mul y

private theorem u5Syl3_card_rootsOfUnity_three (h : UnitaryFieldData 2 2 K) :
    Nat.card (rootsOfUnity 3 K) = 3 := by
  have : Finite K := h.finite
  rw [CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd, u5Syl3_card h]
  norm_num

private theorem u5Syl3_card_range (h : UnitaryFieldData 2 2 K) {lam : K}
    (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0) (h5 : lam ^ 5 = 1) :
    Nat.card (u5Syl3_projB h h2 hlam h5).range = 9 := by
  have : Finite K := h.finite
  rw [MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (u5Syl3_projB_injective h h2 hlam h5),
    Subgroup.card_top, Nat.card_prod, u5Syl3_card_rootsOfUnity_three h]

private theorem u5Syl3_card_statedProj (h : UnitaryFieldData 2 2 K) :
    Nat.card (StatedProj (StatedSU 5 (2 ^ 2) K)) = 9 * (4 ^ 10 * 5663125) := by
  have hK : Nat.card K = (2 ^ 2) ^ 2 := by rw [u5Syl3_card h]; norm_num
  have hprod : (∏ i ∈ Finset.Icc 2 5,
      (((2 ^ 2 : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) = 254840625 := by decide
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (p := 2) (f := 2) (n := 5)
    Nat.prime_two (by norm_num) hK (by norm_num), hprod]
  norm_num

private theorem u5Syl3_factorization_statedProj (h : UnitaryFieldData 2 2 K) :
    (Nat.card (StatedProj (StatedSU 5 (2 ^ 2) K))).factorization 3 = 2 := by
  rw [u5Syl3_card_statedProj h,
    Nat.factorization_mul (by norm_num : (9 : ℕ) ≠ 0)
      (by norm_num : (4 ^ 10 * 5663125 : ℕ) ≠ 0), Finsupp.add_apply]
  have h9 : (9 : ℕ).factorization 3 = 2 := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact Nat.factorization_pow_self (p := 3) (n := 2) Nat.prime_three
  rw [h9, Nat.factorization_eq_zero_of_not_dvd
    (by norm_num : ¬ 3 ∣ 4 ^ 10 * 5663125)]

private def u5Syl3_Dblocks (d : Fin 5 → K) :
    Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin 1) ((Fin 2 ⊕ Fin 2) ⊕ Fin 1) K :=
  Matrix.fromBlocks
    (Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin 2 => d 0)) 0 0
      (Matrix.diagonal (fun _ : Fin 2 => d 2)))
    0 0 (Matrix.diagonal (fun _ : Fin 1 => d 4))

private theorem u5Syl3_reindex_Dblocks (d : Fin 5 → K) (h01 : d 0 = d 1)
    (h23 : d 2 = d 3) :
    Matrix.reindex u5Syl3_e u5Syl3_e (u5Syl3_Dblocks d) = Matrix.diagonal d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u5Syl3_Dblocks, Matrix.reindex_apply, u5Syl3_e_symm_zero, u5Syl3_e_symm_one,
      u5Syl3_e_symm_two, u5Syl3_e_symm_three, u5Syl3_e_symm_four, Matrix.fromBlocks,
      Matrix.diagonal, h01, h23]

private theorem u5Syl3_diagonal_const_comm {m : Type} [Fintype m] [DecidableEq m] (c : K)
    (M : Matrix m m K) :
    Matrix.diagonal (fun _ : m => c) * M = M * Matrix.diagonal (fun _ : m => c) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact mul_comm _ _

private theorem u5Syl3_Dblocks_comm (d : Fin 5 → K)
    (lam : K) (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0)
    (x : rootsOfUnity 3 K × rootsOfUnity 3 K) :
    u5Syl3_Dblocks d * u5Syl3_block lam h2 hlam x =
      u5Syl3_block lam h2 hlam x * u5Syl3_Dblocks d := by
  rw [u5Syl3_Dblocks, u5Syl3_block, u5Syl3_fromBlocks_mul_zero, u5Syl3_fromBlocks_mul_zero,
    u5Syl3_fromBlocks_mul_zero, u5Syl3_fromBlocks_mul_zero]
  simp only [u5Syl3_diagonal_const_comm, one_mul, mul_one]

private theorem u5Syl3_commute_diag (h : UnitaryFieldData 2 2 K) {lam : K}
    (h2 : (2 : K) = 0) (hlam : lam + 1 ≠ 0)
    (A : uU h 5) (d : Fin 5 → K)
    (hd : ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = Matrix.diagonal d)
    (h01 : d 0 = d 1) (h23 : d 2 = d 3)
    (x : rootsOfUnity 3 K × rootsOfUnity 3 K) :
    Commute (A : GL (Fin 5) K) (u5Syl3_Bhom lam h2 hlam x) := by
  apply Units.ext
  show ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
      ((u5Syl3_Bhom lam h2 hlam x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
    ((u5Syl3_Bhom lam h2 hlam x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
      ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
  rw [hd, u5Syl3_coe_Bhom, ← u5Syl3_reindex_Dblocks d h01 h23,
    ← u5Syl3_reindex_mul, ← u5Syl3_reindex_mul,
    u5Syl3_Dblocks_comm d lam h2 hlam x]

theorem exists_u5_sylow_three_fix (h : UnitaryFieldData 2 2 K) :
    ∃ S : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K)), IsPGroup 3 S ∧ ¬ 3 ∣ S.index ∧
      ∀ A : uU h 5, ∀ d : Fin 5 → K,
        ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = Matrix.diagonal d → d 0 = d 1 →
          d 2 = d 3 → ∀ s ∈ S, uConjAut h (n := 5) (by norm_num) A s = s := by
  classical
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨lam, h5, h1⟩ := u5Syl3_exists_lam h
  have hlam : lam + 1 ≠ 0 := u5Syl3_lam_add_one_ne_zero h2 h1
  let S : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K)) := (u5Syl3_projB h h2 hlam h5).range
  have hcard : Nat.card S =
      3 ^ (Nat.card (StatedProj (StatedSU 5 (2 ^ 2) K))).factorization 3 := by
    rw [u5Syl3_factorization_statedProj h]
    exact u5Syl3_card_range h h2 hlam h5
  let P : Sylow 3 (StatedProj (StatedSU 5 (2 ^ 2) K)) := Sylow.ofCard S hcard
  refine ⟨S, P.isPGroup', P.not_dvd_index, ?_⟩
  intro A d hd h01 h23 s hs
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hs
  have hcomm : Commute (A : GL (Fin 5) K) (u5Syl3_Bhom lam h2 hlam x) :=
    u5Syl3_commute_diag h h2 hlam A d hd h01 h23 x
  have hproj : u5Syl3_projB h h2 hlam h5 x =
      projH (StatedSU 5 (2 ^ 2) K)
        ⟨u5Syl3_Bhom lam h2 hlam x, u5Syl3_Bhom_mem_SU h h2 hlam h5 x⟩ := rfl
  rw [hproj, uConjAut_proj]
  congr 1
  apply Subtype.ext
  show (A : GL (Fin 5) K) * u5Syl3_Bhom lam h2 hlam x * (A : GL (Fin 5) K)⁻¹ =
    u5Syl3_Bhom lam h2 hlam x
  rw [hcomm.eq]
  group

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
