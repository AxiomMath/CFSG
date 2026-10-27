module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFSevenN
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFSevenBlk
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFSevenD

public section

namespace CFSG.Quasithin.SBd19F

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

theorem blockHom_nontrivial : ∃ h, proj 3 K (blockHom K h) ≠ 1 := by
  let τ : SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩
  refine ⟨τ, fun h1 => ?_⟩
  rw [proj_eq_one_iff, mem_scalars] at h1
  obtain ⟨c, -, hc⟩ := h1
  have h01 := congrFun (congrFun hc 0) 1
  rw [coe_blockHom] at h01
  simp [τ, blockMat, Matrix.scalar_apply] at h01

theorem symHom_nontrivial : ∃ h, proj 3 K (symHom K h) ≠ 1 := by
  let τ : SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩
  refine ⟨τ, fun h1 => ?_⟩
  rw [proj_eq_one_iff, mem_scalars] at h1
  obtain ⟨c, -, hc⟩ := h1
  have h02 := congrFun (congrFun hc 0) 2
  rw [coe_symHom] at h02
  simp [τ, symMat, Matrix.scalar_apply] at h02

theorem conjAut_diag_fixes_block (Dg : GL (Fin 3) K) (ε ε' : K)
    (hD : (Dg : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![ε, ε, ε'])
    (h : SpecialLinearGroup (Fin 2) K) :
    conjAut 3 K Dg (proj 3 K (blockHom K h)) = proj 3 K (blockHom K h) := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  have hcomm : (Dg : Matrix (Fin 3) (Fin 3) K) *
      ((blockHom K h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((blockHom K h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (Dg : Matrix (Fin 3) (Fin 3) K) := by
    rw [hD, coe_blockHom]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockMat, Matrix.mul_diagonal, Matrix.diagonal_mul] <;> ring
  calc (Dg : Matrix (Fin 3) (Fin 3) K) *
        ((blockHom K h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((Dg⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      = ((blockHom K h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((Dg : Matrix (Fin 3) (Fin 3) K) * ((Dg⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
        rw [hcomm, mul_assoc]
    _ = ((blockHom K h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [Units.mul_inv, mul_one]

theorem not_isSolvable_fixedSub_conjAut [Finite K] (hK4 : 4 ≤ Nat.card K) (h2 : (2 : K) ≠ 0)
    (A : GL (Fin 3) K) (u : Kˣ) (hA : A * A = GeneralLinearGroup.scalar (Fin 3) u) :
    ¬ Group.IsSolvable ↥(SBd18.fixedSub (conjAut 3 K A)) := by
  classical
  have hAA : (A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) =
      (u : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hA
    simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
      using this
  have hdet : (A : Matrix (Fin 3) (Fin 3) K).det * (A : Matrix (Fin 3) (Fin 3) K).det =
      (u : K) ^ 3 := by
    rw [← Matrix.det_mul, hAA, Matrix.det_smul, Matrix.det_one]
    simp
  set μ : K := (u : K) with hμ
  have hμ0 : μ ≠ 0 := u.ne_zero
  set ν : K := (A : Matrix (Fin 3) (Fin 3) K).det / μ with hν
  have hνν : ν * ν = μ := by
    rw [hν]
    field_simp
    linear_combination hdet
  have hν0 : ν ≠ 0 := fun h => hμ0 (by rw [← hνν, h]; ring)
  set S : Matrix (Fin 3) (Fin 3) K := ν⁻¹ • (A : Matrix (Fin 3) (Fin 3) K) with hSdef
  have hS : S * S = 1 := by
    rw [hSdef, Matrix.smul_mul, Matrix.mul_smul, hAA, smul_smul, smul_smul]
    have : ν⁻¹ * ν⁻¹ * μ = 1 := by
      rw [← hνν]
      field_simp
    rw [this, one_smul]
  obtain ⟨B, ε, ε', hB, hε, hε', hSB⟩ := exists_eigenbasis_of_involution h2 hS
  have hε0 : ε ≠ 0 := by rcases hε with h | h <;> rw [h] <;> simp
  have hε'0 : ε' ≠ 0 := by rcases hε' with h | h <;> rw [h] <;> simp
  let D : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![ε, ε, ε']
  have hD : D.det ≠ 0 := by
    simp only [D, det_diagonal, Fin.prod_univ_three]
    simp [hε0, hε'0]
  let Bg : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero B hB
  let Dg : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero D hD
  let ν' : Kˣ := Units.mk0 ν hν0
  have hrel : A * Bg = Bg * (GeneralLinearGroup.scalar (Fin 3) ν' * Dg) := by
    apply Units.ext
    change (A : Matrix (Fin 3) (Fin 3) K) * B = B * (Matrix.scalar (Fin 3) ν * D)
    have hAS : (A : Matrix (Fin 3) (Fin 3) K) = ν • S := by
      rw [hSdef, smul_smul, mul_inv_cancel₀ hν0, one_smul]
    rw [hAS, Matrix.smul_mul, hSB, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
      Matrix.smul_mul, one_mul, Matrix.mul_smul]
  have hA' : conjAut 3 K A = conjAut 3 K Bg * conjAut 3 K Dg * (conjAut 3 K Bg)⁻¹ := by
    have h1 : A = Bg * (GeneralLinearGroup.scalar (Fin 3) ν' * Dg) * Bg⁻¹ :=
      eq_mul_inv_of_mul_eq hrel
    rw [h1, map_mul, map_mul, map_mul, conjAut_scalar, one_mul, map_inv]
  have hDnon := not_isSolvable_fixedSub_of_hom hK4 (blockHom K)
    (fun h => conjAut_diag_fixes_block Dg ε ε' rfl h) blockHom_nontrivial
  rw [hA']
  exact not_isSolvable_fixedSub_conj _ _ hDnon

end CFSG.Quasithin.SBd19F
