module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148BHessMat
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148B

open Matrix
open scoped MatrixGroups

variable {F : Type*} [Field F] {ω : F}

@[expose] def hessH (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) : Subgroup (GL (Fin 3) F) :=
  Subgroup.closure (Set.range (hessT (F := F)) ∪
    Set.range fun k => hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹)

theorem hessT_mem_hessH (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) (k : Fin 3) :
    hessT k ∈ hessH hω h3 :=
  Subgroup.subset_closure (Or.inl ⟨k, rfl⟩)

theorem hessS_mem_hessH (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) (k : Fin 3) :
    hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹ ∈ hessH hω h3 :=
  Subgroup.subset_closure (Or.inr ⟨k, rfl⟩)

theorem hessPhi_conj_mem_hessH (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) {x : GL (Fin 3) F}
    (hx : x ∈ hessH hω h3) : hessPhi hω h3 * x * (hessPhi hω h3)⁻¹ ∈ hessH hω h3 := by
  have hle : (hessH hω h3).map (MulAut.conj (hessPhi hω h3)).toMonoidHom ≤ hessH hω h3 := by
    rw [hessH, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact hessS_mem_hessH hω h3 k
    · change hessPhi hω h3 * (hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹) *
        (hessPhi hω h3)⁻¹ ∈ _
      rw [hessPhi_conj_hessS]
      exact hessT_mem_hessH hω h3 (-k)
  exact hle ⟨x, hx, rfl⟩

@[expose] def blockMat (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]

theorem blockMat_one : blockMat (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat, Matrix.one_apply]

theorem blockMat_mul (A B : Matrix (Fin 2) (Fin 2) F) :
    blockMat (A * B) = blockMat A * blockMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

@[expose] def blockMatHom : Matrix (Fin 2) (Fin 2) F →* Matrix (Fin 3) (Fin 3) F where
  toFun := blockMat
  map_one' := blockMat_one
  map_mul' := blockMat_mul

@[expose] noncomputable def blockHom {k₀ : Type*} [Field k₀] (ψ : k₀ →+* F) :
    SL(2, k₀) →* GL (Fin 3) F :=
  (Units.map (blockMatHom.comp ψ.mapMatrix.toMonoidHom)).comp
    Matrix.SpecialLinearGroup.toGL

theorem coe_blockHom {k₀ : Type*} [Field k₀] (ψ : k₀ →+* F) (A : SL(2, k₀)) :
    ((blockHom ψ A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      blockMat ((A : Matrix (Fin 2) (Fin 2) k₀).map ψ) :=
  rfl

end CFSG.RankThree.PartTwo.Sec4.Ronan148B
