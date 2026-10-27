module

public import CFSG.RankThree.PartTwo.KFacts.KS15Basic
public import CFSG.RankThree.PartTwo.KFacts.KS14SzClassical

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical
open scoped Matrix commutatorElement

theorem permGL_mem_glPi (π : Bool) {n q : ℕ} (hq : q ≠ 0) {K : Type} [Field K]
    (σ : Equiv.Perm (Fin n)) : permGL σ ∈ Sec4.glPi π n q K := by
  cases π
  · refine Subgroup.subset_closure ?_
    change (((permGL σ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (· ^ q))ᵀ *
      ((permGL σ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
    rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, permMatrix_map_pow _ hq,
      Matrix.transpose_permMatrix, inv_inv, ← Matrix.permMatrixHom_apply,
      show Equiv.Perm.permMatrix K σ = Matrix.permMatrixHom σ⁻¹ by
        rw [Matrix.permMatrixHom_apply, inv_inv],
      ← map_mul, inv_mul_cancel, map_one]
  · exact Subgroup.mem_top _

theorem projImage_glPi_nonabelian (π : Bool) {q : ℕ} (hq : q ≠ 0) (K : Type) [Field K] :
    ∃ a b : CFSG.Assembly.RankThreeEven.projImage (Sec4.glPi π 3 q K), a * b ≠ b * a := by
  have h₁ := permGL_mem_glPi π hq (K := K) (Equiv.swap (0 : Fin 3) 1)
  have h₂ := permGL_mem_glPi π hq (K := K) (Equiv.swap (0 : Fin 3) 2)
  refine ⟨⟨_, ⟨_, h₁, rfl⟩⟩, ⟨_, ⟨_, h₂, rfl⟩⟩, fun h => ?_⟩
  have h' := congrArg Subtype.val h
  simp only [Subgroup.coe_mul] at h'
  rw [← map_mul, ← map_mul] at h'
  have hc : ⁅permGL (K := K) (Equiv.swap (0 : Fin 3) 1), permGL (Equiv.swap (0 : Fin 3) 2)⁆ ∈
      Subgroup.center (GL (Fin 3) K) := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm, ← map_mul, ← map_mul]
    exact h'
  rw [← map_commutatorElement, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
  have hne : ⁅Equiv.swap (0 : Fin 3) 1, Equiv.swap (0 : Fin 3) 2⁆ ≠ 1 := by
    decide
  exact permGL_not_mem_statedScalars hne hc

theorem ks15Z3PGLNonabelian : KS15Z3PGLNonabelian := by
  intro X _ p f h
  obtain ⟨π, K, _, hK, -, ⟨e⟩⟩ := h
  have hq : p ^ f ≠ 0 := pow_ne_zero _ hK.prime.ne_zero
  obtain ⟨a, b, hab⟩ := projImage_glPi_nonabelian π hq K
  refine ⟨e.symm (1, a), e.symm (1, b), fun h => hab ?_⟩
  have h' := congrArg e h
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
  exact (Prod.mk.inj h').2

end CFSG.RankThree.PartTwo.KFacts.KS14
