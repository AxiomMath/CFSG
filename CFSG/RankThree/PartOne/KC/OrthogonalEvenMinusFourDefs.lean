module

public import CFSG.RankThree.PartOne.KC.OrthogonalEvenNormPlane
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenNormTail

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module Matrix
open scoped MatrixGroups

section Space

variable {K E : Type} [Field K] [Field E] [Algebra K E]

@[expose] def hermFourSpace (σ : E ≃ₐ[K] E) : Submodule K (Matrix (Fin 2) (Fin 2) E) where
  carrier := {X | ∀ i j, σ (X j i) = X i j}
  add_mem' := fun {X Y} hX hY i j => by
    simp only [Matrix.add_apply, map_add, hX i j, hY i j]
  zero_mem' := fun i j => by simp
  smul_mem' := fun c X hX i j => by
    simp only [Matrix.smul_apply, map_smul, hX i j]

theorem mem_hermFourSpace {σ : E ≃ₐ[K] E} {X : Matrix (Fin 2) (Fin 2) E} :
    X ∈ hermFourSpace σ ↔ ∀ i j, σ (X j i) = X i j :=
  Iff.rfl

@[expose] def hermFourMat (σ : E ≃ₐ[K] E) (a b : K) (z : E) : Matrix (Fin 2) (Fin 2) E :=
  !![algebraMap K E a, z; σ z, algebraMap K E b]

@[expose] def hermFourMatLin (σ : E ≃ₐ[K] E) :
    (((Fin 1 → K) × (Fin 1 → K)) × E) →ₗ[K] Matrix (Fin 2) (Fin 2) E where
  toFun v := hermFourMat σ (v.1.1 0) (v.1.2 0) v.2
  map_add' u v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hermFourMat]
  map_smul' c v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hermFourMat, Algebra.smul_def]

end Space

section Coord

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]
  (D : EvenNormPlane K E)

theorem hermFourMat_mem (a b : K) (z : E) : hermFourMat D.σ a b z ∈ hermFourSpace D.σ := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hermFourMat, D.sigma_sigma]

@[expose] noncomputable def hermFourCoordLin :
    (((Fin 1 → K) × (Fin 1 → K)) × E) →ₗ[K] hermFourSpace D.σ :=
  (hermFourMatLin D.σ).codRestrict (hermFourSpace D.σ) fun v =>
    hermFourMat_mem D (v.1.1 0) (v.1.2 0) v.2

theorem coe_hermFourCoordLin (v : ((Fin 1 → K) × (Fin 1 → K)) × E) :
    ((hermFourCoordLin D v : hermFourSpace D.σ) : Matrix (Fin 2) (Fin 2) E) =
      hermFourMat D.σ (v.1.1 0) (v.1.2 0) v.2 :=
  rfl

theorem hermFourCoordLin_injective : Function.Injective (hermFourCoordLin D) := by
  intro u v h
  have h' := congrArg Subtype.val h
  rw [coe_hermFourCoordLin, coe_hermFourCoordLin] at h'
  have h00 := congrFun (congrFun h' 0) 0
  have h11 := congrFun (congrFun h' 1) 1
  have h01 := congrFun (congrFun h' 0) 1
  simp only [hermFourMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h11 h01
  have e1 := (algebraMap K E).injective h00
  have e2 := (algebraMap K E).injective h11
  refine Prod.ext (Prod.ext (funext fun i => ?_) (funext fun i => ?_)) h01
  · rw [Subsingleton.elim i 0]
    exact e1
  · rw [Subsingleton.elim i 0]
    exact e2

theorem hermFourCoordLin_surjective : Function.Surjective (hermFourCoordLin D) := by
  rintro ⟨X, hX⟩
  obtain ⟨a, ha⟩ := (D.sigma_eq_self_iff (X 0 0)).mp (hX 0 0)
  obtain ⟨b, hb⟩ := (D.sigma_eq_self_iff (X 1 1)).mp (hX 1 1)
  refine ⟨((fun _ => a, fun _ => b), X 0 1), Subtype.ext ?_⟩
  rw [coe_hermFourCoordLin]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermFourMat, ha, hb, ← hX 1 0]

@[expose] noncomputable def hermFourCoord :
    (((Fin 1 → K) × (Fin 1 → K)) × E) ≃ₗ[K] hermFourSpace D.σ :=
  LinearEquiv.ofBijective (hermFourCoordLin D)
    ⟨hermFourCoordLin_injective D, hermFourCoordLin_surjective D⟩

@[expose] noncomputable def hermFourForm : QuadraticForm K (hermFourSpace D.σ) :=
  (evenNormTailForm D.N 1).comp (hermFourCoord D).symm.toLinearMap

end Coord

section Act

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]
  (D : EvenNormPlane K E)

@[expose] def hermFourCongr (σ : E ≃ₐ[K] E) (g : Matrix (Fin 2) (Fin 2) E) :
    Matrix (Fin 2) (Fin 2) E →ₗ[K] Matrix (Fin 2) (Fin 2) E :=
  (LinearMap.mulRight K (g.map σ)ᵀ) ∘ₗ (LinearMap.mulLeft K g)

omit [Finite K] [CharP K 2] in
theorem hermFourCongr_apply (σ : E ≃ₐ[K] E) (g X : Matrix (Fin 2) (Fin 2) E) :
    hermFourCongr σ g X = g * X * (g.map σ)ᵀ :=
  rfl

theorem hermFourCongr_mem (g : Matrix (Fin 2) (Fin 2) E) {X : Matrix (Fin 2) (Fin 2) E}
    (hX : X ∈ hermFourSpace D.σ) : hermFourCongr D.σ g X ∈ hermFourSpace D.σ := by
  intro i j
  have e00 := hX 0 0
  have e01 := hX 0 1
  have e10 := hX 1 0
  have e11 := hX 1 1
  simp only [hermFourCongr_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Fin.sum_univ_two, map_add, map_mul, D.sigma_sigma, e00, e01, e10, e11]
  fin_cases i <;> fin_cases j <;> simp <;> ring

@[expose] noncomputable def hermFourAct (g : Matrix (Fin 2) (Fin 2) E) :
    hermFourSpace D.σ →ₗ[K] hermFourSpace D.σ :=
  (hermFourCongr D.σ g).restrict fun _ hX => hermFourCongr_mem D g hX

@[simp] theorem coe_hermFourAct (g : Matrix (Fin 2) (Fin 2) E) (X : hermFourSpace D.σ) :
    ((hermFourAct D g X : hermFourSpace D.σ) : Matrix (Fin 2) (Fin 2) E) =
      g * (X : Matrix (Fin 2) (Fin 2) E) * (g.map D.σ)ᵀ :=
  rfl

theorem hermFourAct_one : hermFourAct D 1 = 1 := by
  ext X : 2
  simp [Matrix.map_one]

theorem hermFourAct_mul (g h : Matrix (Fin 2) (Fin 2) E) :
    hermFourAct D (g * h) = hermFourAct D g * hermFourAct D h := by
  ext X : 2
  simp only [coe_hermFourAct, Module.End.mul_apply]
  have : (g * h).map D.σ = g.map D.σ * h.map D.σ := Matrix.map_mul (f := (D.σ : E →+* E))
  rw [this, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

@[expose] noncomputable def hermFourEnd : SL(2, E) →* Module.End K (hermFourSpace D.σ) where
  toFun g := hermFourAct D g.1
  map_one' := hermFourAct_one D
  map_mul' g h := hermFourAct_mul D g.1 h.1

@[expose] noncomputable def hermFourRho : SL(2, E) →* (hermFourSpace D.σ ≃ₗ[K] hermFourSpace D.σ) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (hermFourSpace D.σ)).toMonoidHom.comp
    (hermFourEnd D).toHomUnits

theorem coe_hermFourRho (g : SL(2, E)) (X : hermFourSpace D.σ) :
    ((hermFourRho D g X : hermFourSpace D.σ) : Matrix (Fin 2) (Fin 2) E) =
      g.1 * (X : Matrix (Fin 2) (Fin 2) E) * (g.1.map D.σ)ᵀ :=
  rfl

end Act

end CFSG.RankThree.PartOne.KCOrthogonal
