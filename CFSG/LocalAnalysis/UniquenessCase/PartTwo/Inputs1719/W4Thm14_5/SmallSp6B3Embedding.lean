module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherCharTwoOrthonormal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.StatedAPI

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6B3

open Matrix CFSG.Open CFSG.Open.StatedAPI
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section TraceBasis

variable {K L : Type} [Field K] [Finite K] [CharP K 2] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

theorem exists_trace_orthonormal_basis_of_finrank_three (hL : Module.finrank K L = 3) :
    ∃ b : Module.Basis (Fin 3) K L,
      ∀ i j, Algebra.trace K L (b i * b j) = if i = j then 1 else 0 := by
  have hsq : ∀ a : K, IsSquare a := FiniteField.isSquare_of_char_two (ringChar.eq K 2)
  have hnorm : Algebra.traceForm K L (1 : L) 1 ≠ 0 := by
    rw [Algebra.traceForm_apply, one_mul, ← map_one (algebraMap K L),
      Algebra.trace_algebraMap, hL]
    simp [nsmul_eq_mul, show (3 : K) = 1 by
      have := CharTwo.two_eq_zero (R := K)
      linear_combination this]
  obtain ⟨b, hb⟩ := UnitaryHigher.exists_orthonormal_basis_of_charTwo hsq
    (Algebra.traceForm_isSymm K) (traceForm_nondegenerate K L) (Or.inr ⟨1, hnorm⟩)
  refine ⟨b.reindex (finCongr hL), fun i j => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply,
    ← Algebra.traceForm_apply, hb]
  simp only [(finCongr hL).symm.injective.eq_iff]

variable {r : ℕ} (b : Module.Basis (Fin r) K L)
  (hb : ∀ i j, Algebra.trace K L (b i * b j) = if i = j then 1 else 0)

include hb

omit [Finite K] [CharP K 2] [FiniteDimensional K L] [Algebra.IsSeparable K L] in
theorem repr_eq_trace_mul (x : L) (i : Fin r) :
    b.repr x i = Algebra.trace K L (x * b i) := by
  conv_rhs => rw [← b.sum_repr x]
  simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, smul_eq_mul, hb]
  simp

omit [Finite K] [CharP K 2] [FiniteDimensional K L] [Algebra.IsSeparable K L] in
theorem leftMulMatrix_transpose (x : L) :
    (Algebra.leftMulMatrix b x)ᵀ = Algebra.leftMulMatrix b x := by
  ext i j
  simp only [Matrix.transpose_apply, Algebra.leftMulMatrix_eq_repr_mul,
    repr_eq_trace_mul b hb]
  congr 1
  ring

end TraceBasis

section Embedding

variable {K L : Type} [Field K] [Field L] [Algebra K L] {r : ℕ}
  (b : Module.Basis (Fin r) K L)

@[expose] def scalarBlocks (g : SL(2, L)) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  fromBlocks (Algebra.leftMulMatrix b (g 0 0)) (Algebra.leftMulMatrix b (g 0 1))
    (Algebra.leftMulMatrix b (g 1 0)) (Algebra.leftMulMatrix b (g 1 1))

theorem scalarBlocks_one : scalarBlocks b (1 : SL(2, L)) = 1 := by
  simp [scalarBlocks, ← Matrix.fromBlocks_one]

theorem scalarBlocks_mul (g h : SL(2, L)) :
    scalarBlocks b (g * h) = scalarBlocks b g * scalarBlocks b h := by
  rw [scalarBlocks, scalarBlocks, scalarBlocks, Matrix.fromBlocks_multiply]
  congr 1 <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add,
      map_mul]

@[expose] def scalarBlocksHom : SL(2, L) →* Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K where
  toFun := scalarBlocks b
  map_one' := scalarBlocks_one b
  map_mul' := scalarBlocks_mul b

variable (hsym : ∀ x : L, (Algebra.leftMulMatrix b x)ᵀ = Algebra.leftMulMatrix b x)

include hsym

theorem scalarBlocks_symplectic (g : SL(2, L)) :
    (scalarBlocks b g)ᵀ * fromBlocks 0 1 (-1) 0 * scalarBlocks b g =
      fromBlocks 0 1 (-1) 0 := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.property
    change (g : Matrix (Fin 2) (Fin 2) L).det = 1 at h
    rwa [Matrix.det_fin_two] at h
  have hcomm : ∀ x y : L,
      Algebra.leftMulMatrix b x * Algebra.leftMulMatrix b y =
        Algebra.leftMulMatrix b y * Algebra.leftMulMatrix b x := by
    intro x y
    rw [← map_mul, ← map_mul, mul_comm]
  have hdetM : Algebra.leftMulMatrix b (g 0 0) * Algebra.leftMulMatrix b (g 1 1) -
      Algebra.leftMulMatrix b (g 0 1) * Algebra.leftMulMatrix b (g 1 0) = 1 := by
    rw [← map_mul, ← map_mul, ← map_sub, hdet, map_one]
  simp only [scalarBlocks, Matrix.fromBlocks_transpose, hsym, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul, zero_add, add_zero, Matrix.fromBlocks_inj]
  constructor
  · rw [hcomm, neg_add_cancel]
  constructor
  · rw [hcomm (g 1 0) (g 0 1), add_comm, ← sub_eq_add_neg, hdetM]
  constructor
  · rw [hcomm (g 1 1) (g 0 0)]
    have h := congrArg Neg.neg hdetM
    simpa only [neg_sub, sub_eq_add_neg, neg_add, neg_neg, add_comm] using h
  · rw [hcomm, neg_add_cancel]

@[expose] def restrictionSL2 : SL(2, L) →* ↥(StatedSp r K) where
  toFun := fun g => ⟨(scalarBlocksHom b).toHomUnits g, by
    rw [mem_statedSp_iff]
    exact scalarBlocks_symplectic b hsym g⟩
  map_one' := Subtype.ext (map_one (scalarBlocksHom b).toHomUnits)
  map_mul' := fun g h => Subtype.ext (map_mul (scalarBlocksHom b).toHomUnits g h)

theorem coe_restrictionSL2 (g : SL(2, L)) :
    (((restrictionSL2 b hsym g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = scalarBlocks b g := rfl

theorem restrictionSL2_injective : Function.Injective (restrictionSL2 b hsym) := by
  intro g h hgh
  have hM := congrArg (fun x : StatedSp r K =>
    ((x : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hgh
  simp only [coe_restrictionSL2, scalarBlocks, Matrix.fromBlocks_inj] at hM
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact Algebra.leftMulMatrix_injective b hM.1
  · exact Algebra.leftMulMatrix_injective b hM.2.1
  · exact Algebra.leftMulMatrix_injective b hM.2.2.1
  · exact Algebra.leftMulMatrix_injective b hM.2.2.2

theorem coe_restrictionSL2_uElt_one :
    (((restrictionSL2 b hsym (CFSG.QuasithinUnique.Setup.SL2Modules.uElt (1 : L)) :
      StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = fromBlocks 1 1 0 1 := by
  rw [coe_restrictionSL2]
  simp [scalarBlocks, CFSG.QuasithinUnique.Setup.SL2Modules.uElt]

end Embedding

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6B3
