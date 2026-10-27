module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413L33Blk
public import CFSG.GH74.KGroups.L3EpsWreath
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.KGroups.L3Eps
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped MatrixGroups

theorem l33_aut_cases (α : MulAut L33P) :
    α ∈ inner L33P ∨ α * dualAut 3 (ZMod 3) ∈ inner L33P := by
  obtain ⟨A, σ, ε, hε, hα⟩ :=
    (automorphism_generation (K := ZMod 3) (n := 3) le_rfl).2 α
  have hσ : σ = 1 := Subsingleton.elim σ 1
  subst hσ
  rw [hα]
  interval_cases ε
  · left
    simpa [map_one, mul_one] using l33_conjAut_mem_inner A
  · right
    have hδδ : dualAut 3 (ZMod 3) * dualAut 3 (ZMod 3) = 1 :=
      (standard_automorphism_transport (K := ZMod 3) (n := 3)).2.2.2.1
    convert l33_conjAut_mem_inner A using 1
    rw [pow_one, map_one, mul_one, mul_assoc, hδδ, mul_one]

theorem l33_mem_centralizer_zeta (α : MulAut L33P)
    (h : α * MulAut.conj (tInv : L33P) = MulAut.conj (tInv : L33P) * α) :
    ∃ (N : GL (Fin 2) (ZMod 3)) (ε : ℕ), ε ≤ 1 ∧ α = l33Kap N * dualAut 3 (ZMod 3) ^ ε := by
  obtain ⟨A, σ, ε, hε, hα⟩ :=
    (automorphism_generation (K := ZMod 3) (n := 3) le_rfl).2 α
  have hσ : σ = 1 := Subsingleton.elim σ 1
  subst hσ
  rw [map_one, mul_one] at hα
  let D : GL (Fin 3) (ZMod 3) := Matrix.SpecialLinearGroup.toGL dNeg
  have hD : MulAut.conj (tInv : L33P) = conjAut 3 (ZMod 3) D :=
    (conjAut_toGL (K := ZMod 3) (n := 3) (g := dNeg)).symm
  rw [hD] at h
  have hDD : D * D = 1 := by
    show Matrix.SpecialLinearGroup.toGL dNeg * Matrix.SpecialLinearGroup.toGL dNeg = 1
    rw [← map_mul, dNeg_mul_self, map_one]
  have hDsym : (D : Matrix (Fin 3) (Fin 3) (ZMod 3))ᵀ = D := by
    simp only [D]
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_dNeg]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hIT : GeneralLinearGroup.inverseTranspose D = D := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, inv_eq_of_mul_eq_one_right hDD, hDsym]
  have hδD : dualAut 3 (ZMod 3) * conjAut 3 (ZMod 3) D * dualAut 3 (ZMod 3) =
      conjAut 3 (ZMod 3) D := by
    rw [(standard_automorphism_transport (K := ZMod 3) (n := 3)).2.2.2.2.1 D, hIT]
  have hδδ : dualAut 3 (ZMod 3) * dualAut 3 (ZMod 3) = 1 :=
    (standard_automorphism_transport (K := ZMod 3) (n := 3)).2.2.2.1
  have hδcomm : dualAut 3 (ZMod 3) * conjAut 3 (ZMod 3) D =
      conjAut 3 (ZMod 3) D * dualAut 3 (ZMod 3) := by
    have := congrArg (fun x => x * dualAut 3 (ZMod 3)) hδD
    simpa [mul_assoc, hδδ] using this
  have hδpow_comm : ∀ n : ℕ, n ≤ 1 →
      dualAut 3 (ZMod 3) ^ n * conjAut 3 (ZMod 3) D =
        conjAut 3 (ZMod 3) D * dualAut 3 (ZMod 3) ^ n := by
    intro n hn
    interval_cases n
    · simp
    · simpa using hδcomm
  have hAcD : conjAut 3 (ZMod 3) A * conjAut 3 (ZMod 3) D =
      conjAut 3 (ZMod 3) D * conjAut 3 (ZMod 3) A := by
    set δ := dualAut 3 (ZMod 3) ^ ε with hδdef
    have hδδ' : δ * conjAut 3 (ZMod 3) D = conjAut 3 (ZMod 3) D * δ := by
      rw [hδdef]; exact hδpow_comm ε hε
    have hδinv : δ⁻¹ * conjAut 3 (ZMod 3) D = conjAut 3 (ZMod 3) D * δ⁻¹ := by
      have := congrArg (fun x => δ⁻¹ * x * δ⁻¹) hδδ'
      group at this
      exact this.symm
    have hAeq : conjAut 3 (ZMod 3) A = α * δ⁻¹ := by
      rw [hα]; group
    rw [hAeq]
    calc α * δ⁻¹ * conjAut 3 (ZMod 3) D
        = α * (δ⁻¹ * conjAut 3 (ZMod 3) D) := by group
      _ = α * (conjAut 3 (ZMod 3) D * δ⁻¹) := by rw [hδinv]
      _ = (α * conjAut 3 (ZMod 3) D) * δ⁻¹ := by group
      _ = (conjAut 3 (ZMod 3) D * α) * δ⁻¹ := by rw [h]
      _ = conjAut 3 (ZMod 3) D * (α * δ⁻¹) := by group
  have hconj1 : conjAut 3 (ZMod 3) (A * D * A⁻¹ * D⁻¹) = 1 := by
    have hAD : conjAut 3 (ZMod 3) (A * D) = conjAut 3 (ZMod 3) (D * A) := by
      rw [map_mul, map_mul, hAcD]
    have h1 : conjAut 3 (ZMod 3) ((A * D) * (D * A)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hAD, mul_inv_cancel]
    rw [show A * D * A⁻¹ * D⁻¹ = A * D * (D * A)⁻¹ by group]
    exact h1
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (K := ZMod 3) (n := 3) le_rfl
    (A * D * A⁻¹ * D⁻¹) (1 : ZMod 3 ≃+* ZMod 3) (by rw [map_one, mul_one]; exact hconj1)
  have hdetB : GeneralLinearGroup.det (A * D * A⁻¹ * D⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    simp [mul_comm, mul_left_comm, mul_assoc]
  have hc3 : c ^ 3 = 1 := by
    have h := congrArg (GeneralLinearGroup.det) hc
    simpa [hdetB] using h
  have hc1 : c = 1 := by
    have hcube : c ^ 3 = c := by
      clear hc hc3
      revert c
      decide
    exact hcube.symm.trans hc3
  have hB1 : A * D * A⁻¹ * D⁻¹ = 1 := by
    rw [← hc, hc1, map_one]
  have hADcomm : A * D = D * A := by
    have h1 : A * D * A⁻¹ = D := by
      have := congrArg (fun x => x * D) hB1
      simpa [mul_assoc] using this
    have := congrArg (fun x => x * A) h1
    simpa [mul_assoc] using this
  have hAcomm : (A : Matrix (Fin 3) (Fin 3) (ZMod 3)) * (dNeg : SL(3, ZMod 3)).1 =
      (dNeg : SL(3, ZMod 3)).1 * (A : Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
    have := congrArg
      (fun x : GL (Fin 3) (ZMod 3) => (x : Matrix (Fin 3) (Fin 3) (ZMod 3))) hADcomm
    simpa [D, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using this
  obtain ⟨h02, h12, h20, h21⟩ :=
    entries_of_commute_dNeg (F := ZMod 3) (by decide : (2 : ZMod 3) ≠ 0) hAcomm
  let M : Matrix (Fin 3) (Fin 3) (ZMod 3) := (A : Matrix (Fin 3) (Fin 3) (ZMod 3))
  let N₀ : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![M 0 0, M 0 1; M 1 0, M 1 1]
  have hM02 : M 0 2 = 0 := h02
  have hM12 : M 1 2 = 0 := h12
  have hM20 : M 2 0 = 0 := h20
  have hM21 : M 2 1 = 0 := h21
  have hA22 : M 2 2 ≠ 0 := by
    have hAAinv : M * ((A⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h := congrFun (congrFun hAAinv 2) 2
    simp only [Matrix.mul_apply, Fin.sum_univ_three, hM20, hM21, zero_mul, zero_add,
      Matrix.one_apply_eq] at h
    intro h0
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  have hdetM : M.det = N₀.det * M 2 2 := by
    rw [Matrix.det_fin_three, Matrix.det_fin_two]
    simp [N₀, hM02, hM12, hM20, hM21]
    ring
  have hdetN₀ : N₀.det ≠ 0 := by
    intro h0
    have hMdet0 : M.det = 0 := by rw [hdetM, h0, zero_mul]
    exact Matrix.GeneralLinearGroup.det_ne_zero A (by simpa [M] using hMdet0)
  let d : (ZMod 3)ˣ := Units.mk0 (M 2 2) hA22
  have hdval : (d : ZMod 3) = M 2 2 := Units.val_mk0 hA22
  have hdmul : (d : ZMod 3) * ((d⁻¹ : (ZMod 3)ˣ) : ZMod 3) = 1 := Units.mul_inv d
  have hdinvmul : ((d⁻¹ : (ZMod 3)ˣ) : ZMod 3) * (d : ZMod 3) = 1 := Units.inv_mul d
  let N : GL (Fin 2) (ZMod 3) :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (((d⁻¹ : (ZMod 3)ˣ) : ZMod 3) • N₀) (by
      rw [Matrix.det_smul, Fintype.card_fin]
      exact mul_ne_zero (pow_ne_zero 2 (Units.ne_zero (d⁻¹))) hdetN₀)
  have hNcoe : (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      ((d⁻¹ : (ZMod 3)ˣ) : ZMod 3) • N₀ :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _
  have hA22A : (A : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 2 ≠ 0 := hA22
  have hAeq : A = GeneralLinearGroup.scalar (Fin 3) d * l33Blk N := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change M i j = (GeneralLinearGroup.scalar (Fin 3) d * l33Blk N :
      Matrix (Fin 3) (Fin 3) (ZMod 3)) i j
    fin_cases i <;> fin_cases j <;>
      simp [M, N, N₀, d, l33Blk, Units.coe_map, hNcoe, bM,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.scalar_apply, Matrix.diagonal_apply, Fin.sum_univ_three, Fin.sum_univ_two,
        hM02, hM12, hM20, hM21, hdval, hdmul, hdinvmul, mul_assoc] <;>
      field_simp [hA22A]
  refine ⟨N, ε, hε, ?_⟩
  rw [hα, hAeq, map_mul, conjAut_scalar, one_mul]
  rfl

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
