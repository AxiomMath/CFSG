module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.Open.StatedDefs
public import CFSG.Open.StatedAPI
public import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.StandardType.ClassicalPosition

private lemma gSM_exists_dual_pair {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    {u w : V} (huw : LinearIndependent K ![u, w]) :
    ∃ x₁ x₂ : V, B x₁ u = 1 ∧ B x₁ w = 0 ∧ B x₂ u = 0 ∧ B x₂ w = 1 := by
  have hwu : u ∉ Submodule.span K ({w} : Set V) := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨a, ha⟩
    have h0 : (1 : K) • u + (-a) • w = 0 := by rw [neg_smul, ← ha, one_smul]; abel
    exact one_ne_zero (huw.eq_zero_of_pair h0).1
  have hwv : w ∉ Submodule.span K ({u} : Set V) := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨a, ha⟩
    have h0 : a • u + (-1 : K) • w = 0 := by rw [neg_smul, one_smul, ← ha]; abel
    exact neg_ne_zero.mpr one_ne_zero (huw.eq_zero_of_pair h0).2
  obtain ⟨f₁, hf₁u, hf₁ker⟩ :=
    Submodule.exists_le_ker_of_notMem (p := Submodule.span K ({w} : Set V)) hwu
  obtain ⟨f₂, hf₂w, hf₂ker⟩ :=
    Submodule.exists_le_ker_of_notMem (p := Submodule.span K ({u} : Set V)) hwv
  set f₁' : Module.Dual K V := (f₁ u)⁻¹ • f₁ with hf₁'def
  set f₂' : Module.Dual K V := (f₂ w)⁻¹ • f₂ with hf₂'def
  have hf₁'u : f₁' u = 1 := by
    rw [hf₁'def]; simp [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₁u]
  have hf₁'w : f₁' w = 0 := by
    have hmem : w ∈ Submodule.span K ({w} : Set V) := Submodule.subset_span (by simp)
    have hz : f₁ w = 0 := LinearMap.mem_ker.mp (hf₁ker hmem)
    rw [hf₁'def]; simp [LinearMap.smul_apply, hz]
  have hf₂'u : f₂' u = 0 := by
    have hmem : u ∈ Submodule.span K ({u} : Set V) := Submodule.subset_span (by simp)
    have hz : f₂ u = 0 := LinearMap.mem_ker.mp (hf₂ker hmem)
    rw [hf₂'def]; simp [LinearMap.smul_apply, hz]
  have hf₂'w : f₂' w = 1 := by
    rw [hf₂'def]; simp [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₂w]
  refine ⟨(B.toDual hB).symm f₁', (B.toDual hB).symm f₂', ?_, ?_, ?_, ?_⟩
  · rw [← LinearMap.BilinForm.toDual_def hB, LinearEquiv.apply_symm_apply]; exact hf₁'u
  · rw [← LinearMap.BilinForm.toDual_def hB, LinearEquiv.apply_symm_apply]; exact hf₁'w
  · rw [← LinearMap.BilinForm.toDual_def hB, LinearEquiv.apply_symm_apply]; exact hf₂'u
  · rw [← LinearMap.BilinForm.toDual_def hB, LinearEquiv.apply_symm_apply]; exact hf₂'w

private lemma gSM_eichler_apply_one {K V : Type} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] (Q : QuadraticForm K V) {u w : V} (hu : Q u = 0) (hw : Q w = 0)
    (hpol : QuadraticMap.polar Q u w = 0) (c : K) (x : V) :
    CFSG.ClassicalGroups.Orthogonal.eichler Q u (c • w) x =
      x + c • (QuadraticMap.polar Q x u • w + QuadraticMap.polar Q x w • u) := by
  have hpolc : QuadraticMap.polar Q u (c • w) = 0 := by
    rw [QuadraticMap.polar_smul_right, hpol, smul_zero]
  rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply hu hpolc]
  rw [QuadraticMap.polar_smul_right, QuadraticMap.map_smul, hw]
  simp only [smul_zero]
  rw [sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]
  module

theorem exists_eq_eichler_of_mem_siegelGroup {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {u w : V} (hpol : QuadraticMap.polar Q u w = 0) {g : V ≃ₗ[K] V}
    (hg : g ∈ siegelGroup Q u w) :
    ∃ c : K, g = CFSG.ClassicalGroups.Orthogonal.eichler Q u (c • w) := by
  have hg' : g ∈ Subgroup.closure {h : V ≃ₗ[K] V | ∃ c : K,
      h = CFSG.ClassicalGroups.Orthogonal.eichler Q u (c • w)} := hg
  exact Subgroup.closure_induction
    (k := {h : V ≃ₗ[K] V | ∃ c : K,
      h = CFSG.ClassicalGroups.Orthogonal.eichler Q u (c • w)})
    (p := fun h _ => ∃ c : K, h = CFSG.ClassicalGroups.Orthogonal.eichler Q u (c • w))
    (fun x hx => hx)
    ⟨0, by rw [zero_smul, CFSG.ClassicalGroups.Orthogonal.eichler_zero_right]⟩
    (by
      rintro x y hx hy ⟨c, hc⟩ ⟨d, hd⟩
      refine ⟨c + d, ?_⟩
      rw [hc, hd, CFSG.ClassicalGroups.Orthogonal.eichler_mul
        (by rw [QuadraticMap.polar_smul_right, hpol, smul_zero])
        (by rw [QuadraticMap.polar_smul_right, hpol, smul_zero]), add_smul])
    (by
      rintro x hx ⟨c, hc⟩
      refine ⟨-c, ?_⟩
      rw [hc, CFSG.ClassicalGroups.Orthogonal.eichler_inv
        (by rw [QuadraticMap.polar_smul_right, hpol, smul_zero]), neg_smul])
    hg'

theorem range_ker_sub_id_of_mem_siegelGroup {K V : Type} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) {u w : V}
    (huw : LinearIndependent K ![u, w]) (hu : Q u = 0) (hw : Q w = 0)
    (hpol : QuadraticMap.polar Q u w = 0) {g : V ≃ₗ[K] V} (hg : g ∈ siegelGroup Q u w)
    (hg1 : g ≠ 1) :
    LinearMap.range ((g : V →ₗ[K] V) - LinearMap.id) = Submodule.span K {u, w} ∧
      LinearMap.ker ((g : V →ₗ[K] V) - LinearMap.id) =
        LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (Submodule.span K {u, w}) := by
  obtain ⟨c, hc⟩ := exists_eq_eichler_of_mem_siegelGroup hpol hg
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, CFSG.ClassicalGroups.Orthogonal.eichler_zero_right] at hc
    exact hg1 hc
  have hsub : ∀ x : V, (((g : V →ₗ[K] V) - (LinearMap.id : V →ₗ[K] V)) x) =
      c • (QuadraticMap.polar Q x u • w + QuadraticMap.polar Q x w • u) := by
    intro x
    rw [hc, LinearMap.sub_apply, LinearMap.id_apply]
    change CFSG.ClassicalGroups.Orthogonal.eichler Q u (c • w) x - x =
      c • (QuadraticMap.polar Q x u • w + QuadraticMap.polar Q x w • u)
    rw [gSM_eichler_apply_one Q hu hw hpol c x]
    abel
  have hkey : ∀ x, c • (QuadraticMap.polar Q x u • w + QuadraticMap.polar Q x w • u) =
      (c * QuadraticMap.polar Q x u) • w + (c * QuadraticMap.polar Q x w) • u := by
    intro x
    rw [smul_add, smul_smul, smul_smul]
  obtain ⟨x₁, x₂, hx₁u, hx₁w, hx₂u, hx₂w⟩ :=
    gSM_exists_dual_pair (QuadraticMap.polarBilin Q) hnd huw
  rw [QuadraticMap.polarBilin_apply_apply] at hx₁u hx₁w hx₂u hx₂w
  constructor
  · apply le_antisymm
    · rintro y ⟨x, rfl⟩
      rw [hsub x]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
    · refine Submodule.span_le.mpr ?_
      intro y hy
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · refine ⟨c⁻¹ • x₂, ?_⟩
        rw [hsub, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left, hx₂u, hx₂w,
          smul_eq_mul, smul_eq_mul, mul_one, mul_zero, zero_smul, zero_add, smul_smul,
          mul_inv_cancel₀ hc0, one_smul]
      · refine ⟨c⁻¹ • x₁, ?_⟩
        rw [hsub, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left, hx₁u, hx₁w,
          smul_eq_mul, smul_eq_mul, mul_one, mul_zero, zero_smul, add_zero, smul_smul,
          mul_inv_cancel₀ hc0, one_smul]
  · ext x
    constructor
    · intro hx
      rw [LinearMap.mem_ker] at hx
      have hz : QuadraticMap.polar Q x u • w + QuadraticMap.polar Q x w • u = 0 := by
        have h := hx
        rw [hsub x] at h
        exact (smul_eq_zero_iff_right hc0).mp h
      have hpair := huw.eq_zero_of_pair (s := QuadraticMap.polar Q x w)
        (t := QuadraticMap.polar Q x u) (by rw [add_comm]; exact hz)
      rw [LinearMap.BilinForm.mem_orthogonal_span_pair_iff]
      exact ⟨(QuadraticMap.polar_comm Q u x).trans hpair.2,
        (QuadraticMap.polar_comm Q w x).trans hpair.1⟩
    · intro hx
      rw [LinearMap.mem_ker, hsub x]
      rw [LinearMap.BilinForm.mem_orthogonal_span_pair_iff] at hx
      rw [(QuadraticMap.polar_comm Q x u).trans hx.1,
        (QuadraticMap.polar_comm Q x w).trans hx.2]
      simp

end CFSG.StandardType.ClassicalPosition
