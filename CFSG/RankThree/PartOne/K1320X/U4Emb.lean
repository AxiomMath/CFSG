module

public import CFSG.RankThree.PartOne.K1320.SU4Gen
public import CFSG.RankThree.PartOne.KF.R6Su2

public section

namespace CFSG.RankThree.PartOne.K1320X

open Matrix CFSG CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.K1320

variable {K : Type} [Field K]

@[expose] def eSum45 : Fin 4 ⊕ Fin 1 ≃ Fin 5 where
  toFun := Sum.elim ![0, 1, 3, 4] ![2]
  invFun := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inl 2, Sum.inl 3]
  left_inv := by decide
  right_inv := by decide

@[expose] def embMat45 (m : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 5) (Fin 5) K :=
  (Matrix.fromBlocks m 0 0 (1 : Matrix (Fin 1) (Fin 1) K)).submatrix eSum45.symm eSum45.symm

theorem embMat45_apply (m : Matrix (Fin 4) (Fin 4) K) (i j : Fin 5) :
    embMat45 m i j = Matrix.fromBlocks m 0 0 (1 : Matrix (Fin 1) (Fin 1) K)
      (eSum45.symm i) (eSum45.symm j) := rfl

theorem embMat45_mul (m m' : Matrix (Fin 4) (Fin 4) K) :
    embMat45 (m * m') = embMat45 m * embMat45 m' := by
  unfold embMat45
  rw [Matrix.submatrix_mul_equiv _ _ eSum45.symm eSum45.symm eSum45.symm,
    Matrix.fromBlocks_multiply]
  simp

theorem embMat45_one : embMat45 (1 : Matrix (Fin 4) (Fin 4) K) = 1 := by
  unfold embMat45
  rw [Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv eSum45.symm

theorem det_embMat45 (m : Matrix (Fin 4) (Fin 4) K) : (embMat45 m).det = m.det := by
  unfold embMat45
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem conjTr_embMat45 (σ : K ≃+* K) (m : Matrix (Fin 4) (Fin 4) K) :
    conjTr σ (embMat45 m) = embMat45 (conjTr σ m) := by
  unfold conjTr embMat45
  rw [← Matrix.submatrix_map, Matrix.transpose_submatrix, Matrix.fromBlocks_map,
    Matrix.fromBlocks_transpose]
  simp

theorem antidiag_five_eq : (antidiag 5 : Matrix (Fin 5) (Fin 5) K) = embMat45 (antidiag 4) := by
  unfold embMat45
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiag, eSum45, Fin.rev]

theorem embMat45_gram (σ : K ≃+* K) {m : Matrix (Fin 4) (Fin 4) K}
    (hg : conjTr σ m * antidiag 4 * m = antidiag 4) :
    conjTr σ (embMat45 m) * antidiag 5 * embMat45 m = antidiag 5 := by
  rw [conjTr_embMat45, antidiag_five_eq, ← embMat45_mul, ← embMat45_mul, hg]

theorem embMat45_injective : Function.Injective (embMat45 : Matrix (Fin 4) (Fin 4) K → _) := by
  intro m m' H
  ext a b
  have := congrFun (congrFun H (eSum45 (Sum.inl a))) (eSum45 (Sum.inl b))
  simpa [embMat45] using this

@[expose] noncomputable def embGL45 : GL (Fin 4) K →* GL (Fin 5) K where
  toFun g :=
    { val := embMat45 (g : Matrix (Fin 4) (Fin 4) K)
      inv := embMat45 ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      val_inv := by rw [← embMat45_mul, Units.mul_inv, embMat45_one]
      inv_val := by rw [← embMat45_mul, Units.inv_mul, embMat45_one] }
  map_one' := by
    apply Units.ext
    simp [embMat45_one]
  map_mul' g h := by
    apply Units.ext
    simp [embMat45_mul]

variable (σ : K ≃+* K)

@[expose] noncomputable def su4Emb : ↥(SU σ 4) →* ↥(SU σ 5) :=
  (embGL45.comp (SU σ 4).subtype).codRestrict (SU σ 5) (fun g => by
    obtain ⟨hdet, hgram⟩ := mem_SU.1 g.2
    refine mem_SU.mpr ⟨?_, ?_⟩
    · show (embMat45 ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).det = 1
      rw [det_embMat45]
      exact hdet
    · show conjTr σ (embMat45 ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) * antidiag 5 *
        embMat45 ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = antidiag 5
      exact embMat45_gram σ hgram)

theorem gu5_su4Emb (g : ↥(SU σ 4)) :
    gu5 (su4Emb σ g) = embMat45 ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := rfl

theorem su4Emb_injective : Function.Injective (su4Emb σ) := by
  intro g g' H
  apply Subtype.ext
  apply Units.ext
  apply embMat45_injective
  have := congrArg (fun x : ↥(SU σ 5) => gu5 x) H
  simpa only [gu5_su4Emb] using this

theorem embMat45_blk22 (X : Matrix (Fin 2) (Fin 2) K) : embMat45 (blk22 X) = blk25 X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embMat45, eSum45, blk22, blk25]

theorem embMat45_blkB (X : Matrix (Fin 2) (Fin 2) K) : embMat45 (blkB σ X) = blk6 σ X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embMat45, eSum45, blkB, blk6]

variable [CharP K 2]

theorem su4Emb_suBlock (A : SpecialLinearGroup (Fin 2) (fixF σ)) :
    su4Emb σ (suBlock σ A) = su2Emb σ A := by
  apply Subtype.ext
  apply Units.ext
  show embMat45 (blk22 ((liftSL σ A : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) =
    blk25 ((liftSL σ A : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  exact embMat45_blk22 _

theorem su4Emb_suBlockB (hσσ : ∀ x, σ (σ x) = x) (X : SpecialLinearGroup (Fin 2) K) :
    su4Emb σ (suBlockB σ hσσ X) = suBlock6 σ hσσ X := by
  apply Subtype.ext
  apply Units.ext
  show embMat45 (blkB σ (X : Matrix (Fin 2) (Fin 2) K)) = blk6 σ (X : Matrix (Fin 2) (Fin 2) K)
  exact embMat45_blkB σ _

theorem range_su2Emb_sup_suBlock6 [Finite K] {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    (su2Emb (unitaryInvolution K 2 f)).range ⊔
      (suBlock6 (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK)).range =
        (su4Emb (unitaryInvolution K 2 f)).range := by
  have h := suBlock_sup_suBlockB_eq_top hK hf
  have h1 : (su2Emb (unitaryInvolution K 2 f)).range =
      (suBlock (unitaryInvolution K 2 f)).range.map (su4Emb (unitaryInvolution K 2 f)) := by
    ext y
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨suBlock _ A, ⟨A, rfl⟩, su4Emb_suBlock _ A⟩
    · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
      exact ⟨A, (su4Emb_suBlock _ A).symm⟩
  have h2 : (suBlock6 (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK)).range =
      (suBlockB (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK)).range.map
        (su4Emb (unitaryInvolution K 2 f)) := by
    ext y
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨suBlockB _ _ X, ⟨X, rfl⟩, su4Emb_suBlockB _ _ X⟩
    · rintro ⟨_, ⟨X, rfl⟩, rfl⟩
      exact ⟨X, (su4Emb_suBlockB _ _ X).symm⟩
  rw [h1, h2, ← Subgroup.map_sup, h, ← MonoidHom.range_eq_map]

end CFSG.RankThree.PartOne.K1320X
