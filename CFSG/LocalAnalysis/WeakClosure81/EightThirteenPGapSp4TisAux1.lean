module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.Assembly.LowTwoRank (StatedSp)
open Matrix CFSG.LieType.Universal.SpecialLinear

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma wcgapst_permMatrix_mul_inv (σ : Equiv.Perm ι) :
    Equiv.Perm.permMatrix F σ * Equiv.Perm.permMatrix F σ.symm = 1 := by
  rw [← Matrix.permMatrix_mul (σ := σ.symm) (τ := σ)]
  rw [show σ.symm * σ = 1 from by ext x; simp]
  rw [Matrix.permMatrix_one]

noncomputable def wcgapst_permGL (σ : Equiv.Perm ι) : GL ι F :=
  Units.mk (Equiv.Perm.permMatrix F σ) (Equiv.Perm.permMatrix F σ.symm)
    (wcgapst_permMatrix_mul_inv σ) (wcgapst_permMatrix_mul_inv σ.symm)

lemma wcgapst_coe_permGL (σ : Equiv.Perm ι) :
    ((wcgapst_permGL (F := F) σ : GL ι F) : Matrix ι ι F) = Equiv.Perm.permMatrix F σ := by
  rw [wcgapst_permGL]

lemma wcgapst_coe_permGL_inv (σ : Equiv.Perm ι) :
    (((wcgapst_permGL (F := F) σ)⁻¹ : GL ι F) : Matrix ι ι F) =
      Equiv.Perm.permMatrix F σ.symm := by
  simp [wcgapst_permGL]

lemma wcgapst_permMatrix_mul_left (σ : Equiv.Perm ι) (N : Matrix ι ι F) :
    Equiv.Perm.permMatrix F σ.symm * N = N.submatrix σ.symm id :=
  PEquiv.toMatrix_toPEquiv_mul σ.symm N

lemma wcgapst_mul_permMatrix_right (σ : Equiv.Perm ι) (N : Matrix ι ι F) :
    N * Equiv.Perm.permMatrix F σ = N.submatrix id σ.symm := by
  calc N * Equiv.Perm.permMatrix F σ
      = ((Equiv.Perm.permMatrix F σ)ᵀ * Nᵀ)ᵀ := by simp [Matrix.transpose_mul]
    _ = (Equiv.Perm.permMatrix F σ.symm * Nᵀ)ᵀ := by
          rw [Matrix.transpose_permMatrix]; simp [Equiv.Perm.inv_def]
    _ = (Nᵀ.submatrix σ.symm id)ᵀ := by rw [wcgapst_permMatrix_mul_left]
    _ = N.submatrix id σ.symm := by
          ext i j
          simp [Matrix.submatrix_apply, Matrix.transpose_apply]

lemma wcgapst_permMatrix_conj (σ : Equiv.Perm ι) (N : Matrix ι ι F) :
    Equiv.Perm.permMatrix F σ.symm * N * Equiv.Perm.permMatrix F σ =
      N.submatrix σ.symm σ.symm := by
  rw [wcgapst_permMatrix_mul_left, wcgapst_mul_permMatrix_right, Matrix.submatrix_submatrix]
  ext i j
  simp [Function.comp_apply]

@[expose] def wcgapst_wC : Equiv.Perm (Fin 2 ⊕ Fin 2) where
  toFun := fun i => match i with
    | Sum.inl 0 => Sum.inr 1
    | Sum.inl 1 => Sum.inl 0
    | Sum.inr 0 => Sum.inl 1
    | Sum.inr 1 => Sum.inr 0
  invFun := fun i => match i with
    | Sum.inl 0 => Sum.inl 1
    | Sum.inl 1 => Sum.inr 0
    | Sum.inr 0 => Sum.inr 1
    | Sum.inr 1 => Sum.inl 0
  left_inv := by rintro (a | a) <;> fin_cases a <;> rfl
  right_inv := by rintro (a | a) <;> fin_cases a <;> rfl

@[expose] def wcgapst_wAB : Equiv.Perm (Fin 2 ⊕ Fin 2) where
  toFun := fun i => match i with
    | Sum.inl 0 => Sum.inl 1
    | Sum.inl 1 => Sum.inr 0
    | Sum.inr 0 => Sum.inr 1
    | Sum.inr 1 => Sum.inl 0
  invFun := fun i => match i with
    | Sum.inl 0 => Sum.inr 1
    | Sum.inl 1 => Sum.inl 0
    | Sum.inr 0 => Sum.inl 1
    | Sum.inr 1 => Sum.inr 0
  left_inv := by rintro (a | a) <;> fin_cases a <;> rfl
  right_inv := by rintro (a | a) <;> fin_cases a <;> rfl

lemma wcgapst_wC_mem : wcgapst_wC ∈ signedPermGroup 2 := by
  intro x
  rcases x with a | a <;> fin_cases a <;> rfl

lemma wcgapst_wAB_mem : wcgapst_wAB ∈ signedPermGroup 2 := by
  intro x
  rcases x with a | a <;> fin_cases a <;> rfl

noncomputable def wcgapst_nC : StatedSp 2 F :=
  dotW F ⟨wcgapst_wC, wcgapst_wC_mem⟩

noncomputable def wcgapst_nAB : StatedSp 2 F :=
  dotW F ⟨wcgapst_wAB, wcgapst_wAB_mem⟩

lemma wcgapst_coe_nC [CharP F 2] :
    ((wcgapst_nC (F := F) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) =
      wcgapst_permGL wcgapst_wC.symm := by
  rw [wcgapst_nC]
  apply Units.ext
  rw [coe_dotW, wcgapst_coe_permGL]
  ext i j
  simp only [signedPerm_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, dotSign, Sum.elim_inl,
    Sum.elim_inr]
  rcases i with a | a <;> rcases j with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [wcgapst_wC, CharTwo.neg_eq]

lemma wcgapst_coe_nAB [CharP F 2] :
    ((wcgapst_nAB (F := F) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) =
      wcgapst_permGL wcgapst_wAB.symm := by
  rw [wcgapst_nAB]
  apply Units.ext
  rw [coe_dotW, wcgapst_coe_permGL]
  ext i j
  simp only [signedPerm_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, dotSign, Sum.elim_inl,
    Sum.elim_inr]
  rcases i with a | a <;> rcases j with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [wcgapst_wAB, CharTwo.neg_eq]

lemma wcgapst_coe_nC_inv [CharP F 2] :
    (((wcgapst_nC (F := F))⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) =
      wcgapst_permGL wcgapst_wC := by
  rw [Subgroup.coe_inv, wcgapst_coe_nC]
  rfl

lemma wcgapst_coe_nAB_inv [CharP F 2] :
    (((wcgapst_nAB (F := F))⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) =
      wcgapst_permGL wcgapst_wAB := by
  rw [Subgroup.coe_inv, wcgapst_coe_nAB]
  rfl

end CFSG.LocalAnalysis.WeakClosure81

end
