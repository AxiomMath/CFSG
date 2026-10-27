module

public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.Universal.Unitary.Basic

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.LieType.Universal.Unitary Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

@[expose] def spIdx : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim (fun i => Fin.castLE (by omega) i) (fun i => Fin.rev (Fin.castLE (by omega) i))
  invFun j := if h : j.val < 2 then Sum.inl ⟨j.val, h⟩ else Sum.inr ⟨3 - j.val, by omega⟩
  left_inv := by decide
  right_inv := by decide

@[expose] noncomputable def reindexGL {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) : GL ι K ≃* GL κ K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K e).toRingEquiv.toMulEquiv

theorem coe_reindexGL' {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (A : GL ι K) :
    ((reindexGL e A : GL κ K) : Matrix κ κ K) = (A : Matrix ι ι K).submatrix e.symm e.symm := rfl

theorem reindex_J_eq_antidiag [CharP K 2] :
    (Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) K) 1 (-1) 0).submatrix spIdx.symm spIdx.symm =
      antidiag 4 := by
  have h1 : (-1 : K) = 1 := CharTwo.neg_eq 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spIdx, antidiag, Matrix.fromBlocks, Fin.rev, h1]

@[expose] noncomputable def spRev (K : Type) [Field K] : Subgroup (GL (Fin 4) K) :=
  (StatedSp 2 K).map (reindexGL spIdx).toMonoidHom

@[expose] noncomputable def spRevEquiv (K : Type) [Field K] : StatedSp 2 K ≃* spRev K :=
  (reindexGL spIdx).subgroupMap (StatedSp 2 K)

theorem coe_reindexGL_symm {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (A : GL κ K) :
    (((reindexGL e).symm A : GL ι K) : Matrix ι ι K) = (A : Matrix κ κ K).submatrix e e := rfl

theorem mem_spRev_iff [CharP K 2] {A : GL (Fin 4) K} :
    A ∈ spRev K ↔ (A : Matrix (Fin 4) (Fin 4) K)ᵀ * antidiag 4 * (A : Matrix (Fin 4) (Fin 4) K) =
      antidiag 4 := by
  rw [spRev, Subgroup.mem_map_equiv, CFSG.LieType.SteinbergBR.EvenSp.mem_statedSp_iff',
    coe_reindexGL_symm]
  have hJ : Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) K) 1 (-1) 0 =
      (antidiag 4 : Matrix (Fin 4) (Fin 4) K).submatrix spIdx spIdx := by
    rw [← reindex_J_eq_antidiag, Matrix.submatrix_submatrix]
    simp
  rw [hJ, Matrix.transpose_submatrix]
  have e1 : ∀ X Y Z : Matrix (Fin 4) (Fin 4) K,
      X.submatrix spIdx spIdx * Y.submatrix spIdx spIdx * Z.submatrix spIdx spIdx =
        (X * Y * Z).submatrix spIdx spIdx := by
    intro X Y Z
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rw [e1]
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h (spIdx.symm i)) (spIdx.symm j)
    simpa using this
  · intro h
    rw [h]

end CFSG.RankThree.PartOne.KFU
