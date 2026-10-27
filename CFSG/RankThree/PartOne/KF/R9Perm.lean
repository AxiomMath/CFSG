module

public import CFSG.RankThree.PartOne.KF.U4Perm
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescentFixed

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {n p : ℕ} {K : Type} [Field K]

@[expose] noncomputable def permGL : Equiv.Perm (Fin n) →* GL (Fin n) K :=
  (Matrix.permMatrixHom (n := Fin n) (R := K)).toHomUnits

theorem coe_permGL (σ : Equiv.Perm (Fin n)) :
    ((permGL σ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = σ⁻¹.permMatrix K := rfl

theorem coe_permGL_inv (σ : Equiv.Perm (Fin n)) :
    (((permGL σ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = σ.permMatrix K := by
  rw [← map_inv, coe_permGL, inv_inv]

theorem permGL_conj_diagU (σ : Equiv.Perm (Fin n)) (v : Fin n → Kˣ) :
    permGL σ * diagU v * (permGL σ)⁻¹ = diagU (v ∘ σ.symm) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_permGL, coe_permGL_inv, diagU_val, diagU_val]
  have h1 : (σ⁻¹.permMatrix K) * (Matrix.diagonal fun i => (v i : K)) =
      (Matrix.diagonal fun i => (v i : K)).submatrix (σ⁻¹ : Equiv.Perm (Fin n)) id :=
    PEquiv.toMatrix_toPEquiv_mul _ _
  have h2 : ((Matrix.diagonal fun i => (v i : K)).submatrix (σ⁻¹ : Equiv.Perm (Fin n)) id) *
      σ.permMatrix K = ((Matrix.diagonal fun i => (v i : K)).submatrix
        (σ⁻¹ : Equiv.Perm (Fin n)) id).submatrix id σ.symm :=
    PEquiv.mul_toMatrix_toPEquiv _ _
  rw [h1, h2]
  ext k l
  simp only [Matrix.submatrix_apply, id_eq, Matrix.diagonal_apply, Function.comp_apply]
  by_cases hkl : k = l
  · subst hkl
    simp [Equiv.Perm.inv_def]
  · have : σ⁻¹ k ≠ σ.symm l := by
      intro h'
      apply hkl
      have : σ.symm k = σ.symm l := by rw [← Equiv.Perm.inv_def]; exact h'
      exact σ.symm.injective this
    simp [hkl]

theorem det_permGL [CharP K 2] (σ : Equiv.Perm (Fin n)) :
    ((permGL σ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
  rw [coe_permGL, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h
  · simp [h]
  · simp [h, CharTwo.neg_eq]

theorem permGL_mem_unitarySU {f : ℕ} (h : UnitaryFieldData 2 f K) (σ : Equiv.Perm (Fin n)) :
    (permGL σ : GL (Fin n) K) ∈ unitarySU 2 f K n := by
  have : CharP K 2 := h.charP
  rw [mem_unitarySU_iff h]
  refine ⟨det_permGL σ, ?_⟩
  rw [coe_permGL]
  have hm : (σ⁻¹.permMatrix K).map h.bar = σ⁻¹.permMatrix K := by
    ext i j
    simp only [Matrix.map_apply, PEquiv.toMatrix_apply]
    split_ifs <;> simp
  rw [hm, Matrix.transpose_permMatrix, inv_inv, ← Matrix.permMatrix_mul, inv_mul_cancel,
    Matrix.permMatrix_one]

theorem normPerm_permGL (σ : Equiv.Perm (Fin n)) : NormPerm p (permGL σ : GL (Fin n) K) σ := by
  have hconj : ∀ x ∈ torusSU p n K, permGL σ * x * (permGL σ)⁻¹ ∈ torusSU p n K := by
    intro x hx
    obtain ⟨v, hv1, hv2, rfl⟩ := mem_torusSU_iff.mp hx
    rw [permGL_conj_diagU]
    have hv : v ∈ torusVec p n K := ⟨hv1, hv2⟩
    have hy := torusVec_comp σ.symm hv
    exact mem_torusSU_iff.mpr ⟨_, hy.1, hy.2, rfl⟩
  refine ⟨hconj, fun x hx i => ?_⟩
  obtain ⟨v, hv1, hv2, rfl⟩ := mem_torusSU_iff.mp hx
  rw [permGL_conj_diagU]
  simp [ent, diagU_val]

end CFSG.RankThree.PartOne.KFU
