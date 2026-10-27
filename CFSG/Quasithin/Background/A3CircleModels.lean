module

public import CFSG.Assembly.Defs

public section

namespace CFSG.ASVolI.ChA

open scoped MatrixGroups Matrix

section PSL3Aut

variable {F : Type} [Field F]

theorem map_center_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center G' := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩ g
    have := hy (e.symm g)
    have h2 := congrArg e this
    simpa using h2
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    intro g
    have := hx (e g)
    have h2 := congrArg e.symm this
    simpa using h2

@[expose] noncomputable def slConjFun (g : GL (Fin 3) F) (A : SL(3, F)) : SL(3, F) :=
  ⟨(g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) *
      ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), by
    have h : (g : Matrix (Fin 3) (Fin 3) F) *
        ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul]; simp
    have h2 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_one] at h2
    rw [Matrix.det_mul, Matrix.det_mul, A.det_coe, mul_one]
    exact h2⟩

theorem slConjFun_mul (g : GL (Fin 3) F) (A B : SL(3, F)) :
    slConjFun g (A * B) = slConjFun g A * slConjFun g B := by
  apply Subtype.ext
  have h : ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (g : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul]; simp
  rw [Matrix.SpecialLinearGroup.coe_mul]
  show (g : Matrix (Fin 3) (Fin 3) F) * ((A * B : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
      ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    ((g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) *
      ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *
    ((g : Matrix (Fin 3) (Fin 3) F) * (B : Matrix (Fin 3) (Fin 3) F) *
      ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
  rw [Matrix.SpecialLinearGroup.coe_mul]
  calc (g : Matrix (Fin 3) (Fin 3) F) *
        ((A : Matrix (Fin 3) (Fin 3) F) * (B : Matrix (Fin 3) (Fin 3) F)) *
        ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      = (g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) * 1 *
        (B : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
        simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = (g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) *
        (((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F)) *
        (B : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
        rw [h]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem slConjFun_inv_left (g : GL (Fin 3) F) (A : SL(3, F)) :
    slConjFun g⁻¹ (slConjFun g A) = A := by
  apply Subtype.ext
  have h : ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (g : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul]; simp
  show ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) *
        ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *
      (((g⁻¹)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = (A : Matrix (Fin 3) (Fin 3) F)
  rw [inv_inv]
  calc ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) *
          ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) * (g : Matrix (Fin 3) (Fin 3) F)
      = (((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F)) *
          (A : Matrix (Fin 3) (Fin 3) F) *
          (((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F)) := by
        simp only [Matrix.mul_assoc]
    _ = (A : Matrix (Fin 3) (Fin 3) F) := by rw [h, Matrix.one_mul, Matrix.mul_one]

@[expose] noncomputable def slConj (g : GL (Fin 3) F) : SL(3, F) ≃* SL(3, F) where
  toFun := slConjFun g
  invFun := slConjFun g⁻¹
  left_inv A := slConjFun_inv_left g A
  right_inv A := by simpa using slConjFun_inv_left g⁻¹ A
  map_mul' := slConjFun_mul g

@[expose] noncomputable def slField (σ : F ≃+* F) : SL(3, F) ≃* SL(3, F) :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map (σ : F →+* F))
    (Matrix.SpecialLinearGroup.map (σ.symm : F →+* F))
    (by ext A i j; simp) (by ext A i j; simp)

@[expose] noncomputable def pslOfSL (e : SL(3, F) ≃* SL(3, F)) : MulAut PSL(3, F) :=
  QuotientGroup.congr (Subgroup.center SL(3, F)) (Subgroup.center SL(3, F)) e
    (map_center_equiv e)

@[expose] noncomputable def psl3DiagAut (g : GL (Fin 3) F) : MulAut PSL(3, F) :=
  pslOfSL (slConj g)

@[expose] noncomputable def psl3FieldAut (σ : RingAut F) : MulAut PSL(3, F) :=
  pslOfSL (slField σ)

theorem slTranspose_mul (A B : SL(3, F)) :
    (A * B).transpose = B.transpose * A.transpose := by
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_mul]

theorem slTranspose_inv (A : SL(3, F)) : (A⁻¹).transpose = (A.transpose)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← slTranspose_mul, mul_inv_cancel]
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.coe_transpose]

@[expose] noncomputable def slGraph : SL(3, F) ≃* SL(3, F) where
  toFun A := (A⁻¹).transpose
  invFun A := (A.transpose)⁻¹
  left_inv A := by
    show ((((A⁻¹).transpose).transpose))⁻¹ = A
    have : ((A⁻¹).transpose).transpose = A⁻¹ := by
      apply Subtype.ext; simp [Matrix.SpecialLinearGroup.coe_transpose]
    rw [this, inv_inv]
  right_inv A := by
    show ((((A.transpose)⁻¹)⁻¹)).transpose = A
    rw [inv_inv]
    apply Subtype.ext; simp [Matrix.SpecialLinearGroup.coe_transpose]
  map_mul' A B := by
    show ((A * B)⁻¹).transpose = (A⁻¹).transpose * (B⁻¹).transpose
    rw [mul_inv_rev, slTranspose_mul]

@[expose] noncomputable def psl3GraphAut : MulAut PSL(3, F) :=
  pslOfSL slGraph

@[expose] def IsPsl3GraphField (κ : MulAut PSL(3, F)) : Prop :=
  orderOf κ = 2 ∧ ∃ (τ : RingAut F) (g : GL (Fin 3) F), orderOf τ = 2 ∧
    κ = psl3DiagAut g * (psl3GraphAut * psl3FieldAut τ)

@[expose] def psl3Fixed (κ : MulAut PSL(3, F)) : Subgroup PSL(3, F) :=
  (κ : PSL(3, F) ≃* PSL(3, F)).toMonoidHom.eqLocus (MonoidHom.id _)

variable (F) in
@[expose] noncomputable def psl3InnAut : Subgroup (MulAut PSL(3, F)) :=
  (MulAut.conj : PSL(3, F) →* MulAut PSL(3, F)).range

@[expose] noncomputable def psl3Circ (σ : RingAut F) (g : GL (Fin 3) F) :
    Subgroup (MulAut PSL(3, F)) :=
  Subgroup.closure ((psl3InnAut F : Set (MulAut PSL(3, F))) ∪
    {psl3FieldAut σ * psl3DiagAut g})

end PSL3Aut

end CFSG.ASVolI.ChA
