module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Commutator

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

private theorem exists_polar_eq_zero_notMem_span {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) (hd : 3 ≤ Module.finrank K V) {u : V} (hu : Q u = 0)
    (hu0 : u ≠ 0) : ∃ w, polar Q u w = 0 ∧ w ∉ Submodule.span K {u} := by
  let f : Module.Dual K V := polarBilin Q u
  have hf : f ≠ 0 := by
    intro hf0
    refine hu0 (eq_zero_of_polar_eq_zero hQ fun w => ?_)
    have hw := DFunLike.congr_fun hf0 w
    simpa [f, polarBilin_apply_apply] using hw
  have hfin : 2 ≤ Module.finrank K (LinearMap.ker f) := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    omega
  have hspan : Submodule.span K {u} ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    rw [hv]
    exact LinearMap.mem_ker.mpr (by
      simp only [f, polarBilin_apply_apply, polar_self_eq_zero hu])
  have hnot : ¬ LinearMap.ker f ≤ Submodule.span K {u} := by
    intro hle
    have heq : LinearMap.ker f = Submodule.span K {u} := le_antisymm hle hspan
    have h1 : Module.finrank K (LinearMap.ker f) = 1 := by
      rw [heq, finrank_span_singleton hu0]
    omega
  obtain ⟨w, hwk, hws⟩ := SetLike.not_le_iff_exists.mp hnot
  exact ⟨w, by simpa [f, polarBilin_apply_apply] using hwk, hws⟩

theorem mem_span_of_forall_eichler_apply_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    (hd : 3 ≤ Module.finrank K V) {u x : V} (hu : Q u = 0) (hu0 : u ≠ 0)
    (hfix : ∀ w, polar Q u w = 0 → eichler Q u w x = x) : x ∈ Submodule.span K {u} := by
  obtain ⟨w₀, hw₀, hw₀span⟩ := exists_polar_eq_zero_notMem_span hQ hd hu hu0
  have hx_u : polar Q x u = 0 := by
    have h := hfix w₀ hw₀
    rw [eichler_apply hu hw₀] at h
    have hmem : polar Q x u • w₀ ∈ Submodule.span K {u} := by
      have heq : polar Q x u • w₀ = (polar Q x w₀ + Q w₀ * polar Q x u) • u :=
        add_left_cancel (sub_eq_iff_eq_add.mp h)
      rw [heq]
      exact Submodule.mem_span_singleton.mpr ⟨_, rfl⟩
    by_contra hc
    exact hw₀span ((Submodule.smul_mem_iff (p := Submodule.span K {u}) hc).mp hmem)
  have hvan : ∀ w, polar Q u w = 0 → polar Q x w = 0 := by
    intro w hw
    have h := hfix w hw
    simp only [eichler_apply hu hw, hx_u, zero_smul, mul_zero, add_zero] at h
    exact (smul_eq_zero.mp (sub_eq_self.mp h)).resolve_right hu0
  obtain ⟨c, hc⟩ :=
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.exists_smul_of_forall_polar_eq_zero hQ hvan
  exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA
