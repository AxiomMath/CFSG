module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace Matrix

theorem det_eq_zero_of_dual_apply_eq_zero {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Fintype ι] [DecidableEq ι]
    (α : ι → Module.Dual K V) (h : ι → V) {C : Matrix ι ι K}
    (hC : ∀ i j, α i (h j) = C i j) {v : V} (hv : v ≠ 0) (hαv : ∀ i, α i v = 0)
    (hcard : Module.finrank K V ≤ Fintype.card ι) : C.det = 0 := by
  classical
  have hmem : ∀ i, α i ∈ (K ∙ v).dualAnnihilator := by
    intro i
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, hαv i, smul_zero]
  have hnli : ¬ LinearIndependent K α := by
    intro hli
    have hli' : LinearIndependent K (Set.codRestrict α (K ∙ v).dualAnnihilator hmem) :=
      hli.codRestrict _ hmem
    haveI : Module.Finite K (K ∙ v).dualAnnihilator :=
      FiniteDimensional.finiteDimensional_submodule _
    have hle : Fintype.card ι ≤ Module.finrank K (K ∙ v).dualAnnihilator :=
      hli'.fintype_card_le_finrank
    have hdim : Module.finrank K V = 1 + Module.finrank K (K ∙ v).dualAnnihilator := by
      have h := Subspace.finrank_add_finrank_dualAnnihilator_eq (K ∙ v : Submodule K V)
      have hv1 : Module.finrank K (K ∙ v : Submodule K V) = 1 := finrank_span_singleton hv
      omega
    omega
  obtain ⟨c, hcsum, i, hci⟩ := Fintype.not_linearIndependent_iff.mp hnli
  have hcne : c ≠ 0 := by
    intro hc
    exact hci (by simp [hc])
  have hvec : c ᵥ* C = 0 := by
    funext j
    rw [Matrix.vecMul_apply_eq_sum]
    have h1 : (∑ i, c i • α i) (h j) = 0 := by simp [hcsum]
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    simpa [hC] using h1
  exact Matrix.exists_vecMul_eq_zero_iff.mp ⟨c, hcne, hvec⟩

end Matrix

end
