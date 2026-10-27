module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Diag

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open
open scoped Matrix MatrixGroups

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

private theorem exists_sq_eq (a : S.Kˣ) : ∃ r : S.Kˣ, r * r = a :=
  Finite.surjective_of_injective (f := fun x : S.Kˣ => x * x) (by
    intro x y h
    apply Units.ext
    exact CharTwo.sq_inj.mp (by
      have h' := congrArg (fun u : S.Kˣ => (u : S.K)) h
      simpa [pow_two, Units.val_mul] using h')) a

private def diagSL (u : S.Kˣ) : SL(2, S.K) :=
  ⟨Matrix.diagonal ![(u : S.K), ((u⁻¹ : S.Kˣ) : S.K)], by
    rw [Matrix.det_diagonal]
    simp [Fin.prod_univ_two]⟩

private theorem vec_jHom_diagSL (s t : S.Kˣ) (w : W) :
    S.vec (S.jHom (diagSL S s, diagSL S t) w) =
      fun i => (OmegaEig.torusVals (s * t) (s * t⁻¹) i : S.K) * S.vec w i := by
  rw [S.vec_jHom]
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [OmegaEig.torusVals, Sum.elim_inl, Sum.elim_inr, ofMat, toMat, diagSL,
      Matrix.diagonal_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      Fin.rev] <;>
    ring

theorem actHom_torus_mem_omega (α β : S.Kˣ) :
    S.actHom (OmegaEig.diagGL (OmegaEig.torusVals α β)) ∈ S.omega := by
  obtain ⟨s, hs⟩ := exists_sq_eq S (α * β)
  obtain ⟨t, ht⟩ := exists_sq_eq S (α * β⁻¹)
  have hsK : (s : S.K) * (s : S.K) = (α : S.K) * (β : S.K) := by
    simpa [Units.val_mul] using congrArg (fun u : S.Kˣ => (u : S.K)) hs
  have htK : (t : S.K) * (t : S.K) = (α : S.K) * ((β⁻¹ : S.Kˣ) : S.K) := by
    simpa [Units.val_mul] using congrArg (fun u : S.Kˣ => (u : S.K)) ht
  have hst : s * t = α := by
    apply Units.ext
    apply CharTwo.sq_inj.mp
    calc ((s * t : S.Kˣ) : S.K) ^ 2
        = ((s : S.K) * (t : S.K)) * ((s : S.K) * (t : S.K)) := by
            rw [pow_two, Units.val_mul]
      _ = ((s : S.K) * (s : S.K)) * ((t : S.K) * (t : S.K)) := by ring
      _ = ((α : S.K) * (β : S.K)) * ((α : S.K) * ((β⁻¹ : S.Kˣ) : S.K)) := by rw [hsK, htK]
      _ = (α : S.K) ^ 2 := by
            rw [pow_two, Units.val_inv_eq_inv_val]
            field_simp [Units.ne_zero β]
  have hst' : s * t⁻¹ = β := by
    apply Units.ext
    apply CharTwo.sq_inj.mp
    calc ((s * t⁻¹ : S.Kˣ) : S.K) ^ 2
        = ((s : S.K) * ((t : S.K))⁻¹) * ((s : S.K) * ((t : S.K))⁻¹) := by
            rw [pow_two, Units.val_mul, Units.val_inv_eq_inv_val]
      _ = ((s : S.K) * (s : S.K)) * (((t : S.K) * (t : S.K))⁻¹) := by
            field_simp [Units.ne_zero t]
      _ = ((α : S.K) * (β : S.K)) * (((α : S.K) * ((β⁻¹ : S.Kˣ) : S.K))⁻¹) := by
            rw [hsK, htK]
      _ = (β : S.K) ^ 2 := by
            rw [pow_two, Units.val_inv_eq_inv_val]
            field_simp [Units.ne_zero β]
  have hEq : S.actHom (OmegaEig.diagGL (OmegaEig.torusVals α β)) =
      S.jHom (diagSL S s, diagSL S t) := by
    apply MulEquiv.ext
    intro w
    apply S.vec_injective
    rw [S.actHom_vec, OmegaEig.diagGL_mulVec, S.vec_jHom_diagSL s t w, hst, hst']
  rw [hEq]
  exact S.omega0_le_omega (show S.jHom (diagSL S s, diagSL S t) ∈ S.jHom.range from
    MonoidHom.mem_range.mpr ⟨(diagSL S s, diagSL S t), rfl⟩)

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
