module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofMinusU4Mat
public import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofMinusL4
public import CFSG.GH74.Generic.S3.LyVertSL2

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG Matrix
open CFSG.LieType.Universal.Unitary (conjTr antidiag SUid)
open scoped MatrixGroups

namespace Item211Res4Proof

open Item228Census3Proof Item228Census5Proof

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem coe_reindexV₄_symm (g : GL (Fin 4) K) :
    (((reindexV₄ K).symm g : GL V₄ K) : Matrix V₄ V₄ K) =
      (g : Matrix (Fin 4) (Fin 4) K).submatrix idxV₄ idxV₄ :=
  rfl

theorem coordZ_mul_reindex (Z : GL V₄ K) (Q X : GL (Fin 4) K) :
    coordZ (Z * (reindexV₄ K).symm Q) X = Z * (reindexV₄ K).symm (Q * X * Q⁻¹) * Z⁻¹ := by
  rw [coordZ_apply, map_mul, map_mul, map_inv]
  group

theorem submatrix_diagonal_four (x y : K) :
    (diagonal ![x, x, y, y]).submatrix idxV₄ idxV₄ =
      fromBlocks (x • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 (y • 1) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [idxV₄_inl_zero, idxV₄_inl_one, idxV₄_inr_zero, idxV₄_inr_one, Matrix.diagonal]

variable (σ : K ≃+* K)

@[expose] def IsFormQ (h : GL V₄ K) : Prop :=
  (h : Matrix V₄ V₄ K).det = 1 ∧
    cstar σ (h : Matrix V₄ V₄ K) * formQ * (h : Matrix V₄ V₄ K) = formQ

variable {σ}

theorem mem_SUid_iff_formQ {Q : GL (Fin 4) K}
    (hQ : ∀ g, g ∈ SUid σ 4 ↔ Q * g * Q⁻¹ ∈ CFSG.LieType.Universal.Unitary.SU σ 4)
    (Z : GL V₄ K) (hZ : cstar σ (Z : Matrix V₄ V₄ K) * formQ * (Z : Matrix V₄ V₄ K) = formV)
    (X : GL (Fin 4) K) :
    X ∈ SUid σ 4 ↔ IsFormQ σ (coordZ (Z * (reindexV₄ K).symm Q) X) := by
  rw [hQ X, mem_SU_iff_blocks, IsFormQ, coordZ_mul_reindex]
  set g := Q * X * Q⁻¹
  have hdet : ((Z * (reindexV₄ K).symm g * Z⁻¹ : GL V₄ K) : Matrix V₄ V₄ K).det =
      (g : Matrix (Fin 4) (Fin 4) K).det := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
      ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul,
      coe_reindexV₄_symm, Matrix.det_submatrix_equiv_self]
  rw [hdet]
  refine and_congr_right fun _ => ?_
  rw [← coe_reindexV₄_symm]
  exact cstar_conj_iff hZ (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) _

theorem isFormQ_blkDiag {B : SL(2, K)} (hB : (B : Matrix (Fin 2) (Fin 2) K).map σ = B) :
    IsFormQ σ (blkDiag B) := by
  refine ⟨?_, ?_⟩
  · have := blkDiag_mem_ker B
    rw [MonoidHom.mem_ker] at this
    have e := congrArg Units.val this
    rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at e
  · rw [coe_blkDiag]
    exact cstar_blk_formQ_of_fixed hB B.2

theorem cstar_jMat_of_formQ {x : Matrix V₄ V₄ K} {Y : Matrix (Fin 2) (Fin 2) K}
    (hx : cstar σ x * formQ * x = formQ)
    (h : cstar σ (x * fromBlocks Y 0 0 Y) * formQ * (x * fromBlocks Y 0 0 Y) = formQ) :
    cstar σ Y * jMat * Y = jMat := by
  apply cstar_jMat_of_blk
  rw [cstar_mul] at h
  calc cstar σ (fromBlocks Y 0 0 Y) * formQ * fromBlocks Y 0 0 Y =
      cstar σ (fromBlocks Y 0 0 Y) * (cstar σ x * formQ * x) * fromBlocks Y 0 0 Y := by rw [hx]
    _ = cstar σ (fromBlocks Y 0 0 Y) * cstar σ x * formQ * (x * fromBlocks Y 0 0 Y) := by
        simp only [Matrix.mul_assoc]
    _ = formQ := h

section Fixed

variable (F : Subfield K)

@[expose] noncomputable def mapF : SL(2, F) →* SL(2, K) :=
  SpecialLinearGroup.map F.subtype

theorem coe_mapF (B : SL(2, F)) :
    ((mapF F B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      (B : Matrix (Fin 2) (Fin 2) F).map F.subtype :=
  rfl

theorem mapF_injective : Function.Injective (mapF F) := by
  intro B B' h
  apply Subtype.ext
  ext i j
  exact congrArg (fun M : SL(2, K) => (M : Matrix (Fin 2) (Fin 2) K) i j) h

theorem exists_mapF_eq {M : SL(2, K)} (hM : ∀ i j, (M : Matrix (Fin 2) (Fin 2) K) i j ∈ F) :
    ∃ B : SL(2, F), mapF F B = M := by
  let A : Matrix (Fin 2) (Fin 2) F := Matrix.of fun i j => ⟨_, hM i j⟩
  have e : F.subtype.mapMatrix A = (M : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    rfl
  have hA : A.det = 1 := by
    apply Subtype.ext
    have := RingHom.map_det F.subtype A
    rw [e, M.2] at this
    exact this
  exact ⟨⟨A, hA⟩, Subtype.ext e⟩

variable {F}

theorem exists_beta [Finite F] (hF : ∀ c, c ∈ F ↔ σ c = c) (Y : GL (Fin 2) K)
    (hY : cstar σ (Y : Matrix (Fin 2) (Fin 2) K) * jMat * (Y : Matrix (Fin 2) (Fin 2) K) = jMat) :
    ∃ β : MulAut SL(2, F), ∀ B, mapF F (β B) = CFSG.GH74.Generic.S3.glConj Y (mapF F B) := by
  classical
  set Ym := (Y : Matrix (Fin 2) (Fin 2) K)
  set Yi := ((Y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  have hYYi : Ym * Yi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hYi : cstar σ Yi * jMat * Yi = jMat := by
    calc cstar σ Yi * jMat * Yi = cstar σ Yi * (cstar σ Ym * jMat * Ym) * Yi := by rw [hY]
      _ = cstar σ (Ym * Yi) * jMat * (Ym * Yi) := by
          rw [cstar_mul]
          simp only [Matrix.mul_assoc]
      _ = jMat := by rw [hYYi, cstar_one, Matrix.one_mul, Matrix.mul_one]
  have hfix : ∀ B : SL(2, F), ∀ i j,
      ((CFSG.GH74.Generic.S3.glConj Y (mapF F B) : SL(2, K)) :
        Matrix (Fin 2) (Fin 2) K) i j ∈ F := by
    intro B i j
    set M := ((CFSG.GH74.Generic.S3.glConj Y (mapF F B) : SL(2, K)) :
      Matrix (Fin 2) (Fin 2) K)
    have hBfix : ((mapF F B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).map σ =
        (mapF F B : SL(2, K)) := by
      ext k l
      rw [Matrix.map_apply, coe_mapF, Matrix.map_apply]
      exact (hF _).mp (B.1 k l).2
    have hBj : cstar σ ((mapF F B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * jMat *
        ((mapF F B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = jMat := by
      rw [cstar_eq_transpose σ hBfix, transpose_mul_jMat_mul, (mapF F B).2, one_smul]
    have hMj : cstar σ M * jMat * M = jMat := by
      have eM : M = Ym * ((mapF F B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * Yi :=
        CFSG.GH74.Generic.S3.coe_glConj _ _
      rw [eM, cstar_mul, cstar_mul]
      calc cstar σ Yi * (cstar σ ((mapF F B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
          cstar σ Ym) * jMat * (Ym * ((mapF F B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * Yi) =
          cstar σ Yi * (cstar σ ((mapF F B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
            (cstar σ Ym * jMat * Ym) * ((mapF F B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) *
              Yi := by
            simp only [Matrix.mul_assoc]
        _ = jMat := by rw [hY, hBj, hYi]
    have hM := map_eq_of_cstar_jMat σ (CFSG.GH74.Generic.S3.glConj Y (mapF F B)).2 hMj
    exact (hF _).mpr (congrFun (congrFun hM i) j)
  let f : SL(2, F) →* SL(2, F) :=
    ((MonoidHom.ofInjective (mapF_injective F)).symm.toMonoidHom).comp
      (((CFSG.GH74.Generic.S3.glConj Y).toMonoidHom.comp (mapF F)).codRestrict (mapF F).range
        fun B => by
          obtain ⟨B', hB'⟩ := exists_mapF_eq F (hfix B)
          exact ⟨B', hB'⟩)
  have hf : ∀ B, mapF F (f B) = CFSG.GH74.Generic.S3.glConj Y (mapF F B) := by
    intro B
    change mapF F ((MonoidHom.ofInjective (mapF_injective F)).symm _) = _
    rw [← MonoidHom.ofInjective_apply (mapF_injective F), MulEquiv.apply_symm_apply]
    rfl
  have hinj : Function.Injective f := by
    intro B B' h
    apply mapF_injective F
    apply (CFSG.GH74.Generic.S3.glConj Y).injective
    rw [← hf, ← hf, h]
  have : Finite (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Finite (Fin 2 → Fin 2 → F))
  have : Finite SL(2, F) := Finite.of_injective _ Subtype.coe_injective
  exact ⟨MulEquiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), hf⟩

end Fixed

end Item211Res4Proof

end CFSG.RankThree.PartTwo.Sec21
