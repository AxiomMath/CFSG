module

public import CFSG.RankThree.PartOne.KC.SymplecticFourTransvectionDefs
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData

public section

namespace CFSG.RankThree.PartOne.KCSymplecticFour

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {K : Type} [Field K]

@[expose] def coordIndex : Fin 4 ≃ Fin 2 ⊕ Fin 2 where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inr 1, Sum.inr 0]
  invFun := Sum.elim ![0, 1] ![3, 2]
  left_inv := by intro x; fin_cases x <;> rfl
  right_inv := by intro x; rcases x with x | x <;> fin_cases x <;> rfl

@[expose] def coordAlg (K : Type) [Field K] :
    Matrix (Fin 4) (Fin 4) K ≃ₐ[K] Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.reindexAlgEquiv K K coordIndex

theorem coordAlg_apply (M : Matrix (Fin 4) (Fin 4) K) :
    coordAlg K M = Matrix.reindex coordIndex coordIndex M :=
  rfl

theorem coordAlg_transpose (M : Matrix (Fin 4) (Fin 4) K) :
    coordAlg K Mᵀ = (coordAlg K M)ᵀ := by
  rw [coordAlg_apply, coordAlg_apply, Matrix.transpose_reindex]

@[expose] def coordGL (K : Type) [Field K] : GL (Fin 4) K ≃* GL (Fin 2 ⊕ Fin 2) K :=
  Units.mapEquiv (coordAlg K).toMulEquiv

theorem coe_coordGL (g : GL (Fin 4) K) :
    ((coordGL K g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      coordAlg K (g : Matrix (Fin 4) (Fin 4) K) :=
  rfl

theorem coordAlg_gram : coordAlg K (symplecticFourGram K) = formJ 2 K := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [coordAlg_apply, coordIndex, symplecticFourGram, formJ]

theorem coordAlg_conj_gram (M : Matrix (Fin 4) (Fin 4) K) :
    (coordAlg K M)ᵀ * formJ 2 K * coordAlg K M =
      coordAlg K (Mᵀ * symplecticFourGram K * M) := by
  rw [map_mul, map_mul, coordAlg_transpose, coordAlg_gram]

theorem coordGL_mem_statedSp {g : GL (Fin 4) K} :
    coordGL K g ∈ StatedSp 2 K ↔ g ∈ symplecticFourS K := by
  rw [SymplecticTorusWeyl.mem_statedSp_iff]
  change (coordAlg K (g : Matrix (Fin 4) (Fin 4) K))ᵀ * fromBlocks 0 1 (-1) 0 *
      coordAlg K (g : Matrix (Fin 4) (Fin 4) K) = fromBlocks 0 1 (-1) 0 ↔
    (g : Matrix (Fin 4) (Fin 4) K)ᵀ * symplecticFourGram K * g = symplecticFourGram K
  have h := coordAlg_conj_gram (g : Matrix (Fin 4) (Fin 4) K)
  change _ = _ at h
  rw [show (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = formJ 2 K from
    rfl, h, ← coordAlg_gram (K := K)]
  exact (coordAlg K).injective.eq_iff

theorem map_symplecticFourS :
    (symplecticFourS K).map (coordGL K).toMonoidHom = StatedSp 2 K := by
  ext x
  rw [Subgroup.mem_map_equiv, ← coordGL_mem_statedSp, MulEquiv.apply_symm_apply]

@[expose] def spEquiv (K : Type) [Field K] : symplecticFourS K ≃* StatedSp 2 K :=
  ((coordGL K).subgroupMap (symplecticFourS K)).trans
    (MulEquiv.subgroupCongr (map_symplecticFourS (K := K)))

theorem coe_spEquiv (g : symplecticFourS K) :
    ((spEquiv K g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) = coordGL K (g : GL (Fin 4) K) :=
  rfl

theorem coordAlg_map (σ : K ≃+* K) (M : Matrix (Fin 4) (Fin 4) K) :
    (coordAlg K M).map σ = coordAlg K (M.map σ) := by
  ext i j
  simp [coordAlg_apply, Matrix.reindex_apply]

theorem coordAlg_E14 :
    coordAlg K (symplecticFourE14 K) = Matrix.single (Sum.inl 0) (Sum.inr 0) (1 : K) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [coordAlg_apply, coordIndex, symplecticFourE14]

theorem coe_spEquiv_transvection (c : K) :
    (((spEquiv K (symplecticFourTransvection K c) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      1 + Matrix.single (Sum.inl 0) (Sum.inr 0) c := by
  rw [coe_spEquiv, coe_coordGL, coe_symplecticFourTransvection, map_add, map_one, map_smul,
    coordAlg_E14, Matrix.smul_single, smul_eq_mul, mul_one]

end CFSG.RankThree.PartOne.KCSymplecticFour
