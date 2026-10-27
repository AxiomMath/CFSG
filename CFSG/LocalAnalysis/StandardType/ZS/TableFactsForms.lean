module

public import CFSG.LocalAnalysis.StandardType.ZS.ExcMatrices
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS.TableFacts

variable {p : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W] [Module (ZMod p) W]

@[expose] noncomputable def basisDiagForm {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) W)
    (w : Fin n → ZMod p) : QuadraticForm (ZMod p) W :=
  (QuadraticMap.weightedSumSquares (ZMod p) w).comp
    (f.equivFun : W →ₗ[ZMod p] Fin n → ZMod p)

theorem basisDiagForm_nondegenerate (hp : p ≠ 2) {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) W)
    {w : Fin n → ZMod p} (hw : ∀ i, w i ≠ 0) :
    (QuadraticMap.polarBilin (basisDiagForm f w)).Nondegenerate := by
  let _ : Invertible (2 : ZMod p) := invertibleOfNonzero (by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out) (by norm_num)).mp hdvd))
  have hQ : (QuadraticMap.weightedSumSquares (ZMod p) w).Nondegenerate := by
    refine QuadraticMap.nondegenerate_weightedSumSquares fun i => ?_
    rw [isRegular_iff_ne_zero]
    exact hw i
  have hB : (QuadraticMap.polarBilin
      (QuadraticMap.weightedSumSquares (ZMod p) w)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have h_eq : QuadraticMap.polarBilin (basisDiagForm f w) =
      LinearMap.BilinForm.congr f.equivFun.symm
        (QuadraticMap.polarBilin (QuadraticMap.weightedSumSquares (ZMod p) w)) := by
    ext x y
    simp [basisDiagForm, QuadraticMap.polarBilin_comp, LinearMap.BilinForm.congr_apply]
  rw [h_eq]
  exact LinearMap.BilinForm.Nondegenerate.congr f.equivFun.symm hB

theorem isIsom_basisDiagForm_of_toMatrix {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) W)
    (w : Fin n → ZMod p) {g : W ≃ₗ[ZMod p] W}
    (hg : (LinearMap.toMatrix f f (g : W →ₗ[ZMod p] W)).transpose * Matrix.diagonal w *
      LinearMap.toMatrix f f (g : W →ₗ[ZMod p] W) = Matrix.diagonal w) :
    IsIsom p (basisDiagForm f w) g := by
  intro v
  let M := LinearMap.toMatrix f f (g : W →ₗ[ZMod p] W)
  have hx : f.repr (g v) = M.mulVec (f.repr v) := by
    change f.repr (g v) =
      (LinearMap.toMatrix f f (g : W →ₗ[ZMod p] W)).mulVec (f.repr v)
    exact (LinearMap.toMatrix_mulVec_repr (v₁ := f) (v₂ := f)
      (f := (g : W →ₗ[ZMod p] W)) v).symm
  have hQ_apply : ∀ y : Fin n → ZMod p,
      QuadraticMap.weightedSumSquares (ZMod p) w y =
        dotProduct y ((Matrix.diagonal w).mulVec y) := by
    intro y
    simp [QuadraticMap.weightedSumSquares_apply, Matrix.mulVec_diagonal, dotProduct,
      smul_eq_mul, mul_left_comm]
  simp only [basisDiagForm, QuadraticMap.comp_apply]
  change QuadraticMap.weightedSumSquares (ZMod p) w (f.repr (g v)) =
    QuadraticMap.weightedSumSquares (ZMod p) w (f.repr v)
  rw [hx]
  calc QuadraticMap.weightedSumSquares (ZMod p) w (M.mulVec (f.repr v))
      = dotProduct (M.mulVec (f.repr v))
          ((Matrix.diagonal w).mulVec (M.mulVec (f.repr v))) := hQ_apply _
    _ = dotProduct (f.repr v)
          (M.transpose.mulVec ((Matrix.diagonal w).mulVec (M.mulVec (f.repr v)))) := by
        rw [dotProduct_comm]
        rw [← Matrix.dotProduct_transpose_mulVec]
    _ = dotProduct (f.repr v)
          ((M.transpose * Matrix.diagonal w * M).mulVec (f.repr v)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = dotProduct (f.repr v) ((Matrix.diagonal w).mulVec (f.repr v)) := by rw [hg]
    _ = QuadraticMap.weightedSumSquares (ZMod p) w (f.repr v) := (hQ_apply _).symm

theorem isIsom_basisDiagForm_of_mem_basisClosure {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) W)
    (w : Fin n → ZMod p) {S : Set (Matrix (Fin n) (Fin n) (ZMod p))}
    (hS : ∀ M ∈ S, M.transpose * Matrix.diagonal w * M = Matrix.diagonal w)
    {g : W ≃ₗ[ZMod p] W} (hg : g ∈ basisClosure f S) : IsIsom p (basisDiagForm f w) g := by
  refine Subgroup.closure_induction
    (k := {g : W ≃ₗ[ZMod p] W | LinearMap.toMatrix f f (g : W →ₗ[ZMod p] W) ∈ S})
    ?_ ?_ ?_ ?_ hg
  · intro x hx
    exact isIsom_basisDiagForm_of_toMatrix f w
      (hS (LinearMap.toMatrix f f (x : W →ₗ[ZMod p] W)) hx)
  · intro v
    rfl
  · intro x y hx hy ihx ihy v
    simp only [LinearEquiv.mul_apply]
    rw [ihx (y v), ihy v]
  · intro x hx ih v
    have h := ih (x⁻¹ v)
    rw [show x (x⁻¹ v) = v from by simp] at h
    exact h.symm

end CFSG.StandardType.ZS.TableFacts

end
