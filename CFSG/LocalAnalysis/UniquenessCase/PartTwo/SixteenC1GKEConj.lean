module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GKEW

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LargeExtraspecial.O62 Subgroup

private lemma s16c1c_conj_apply (g x : V₀ ≃ₗ[ZMod 2] V₀) (u : V₀) :
    (g⁻¹ * x * g) (g⁻¹ u) = g⁻¹ (x u) := by
  simp [mul_apply]

private lemma s16c1c_conj_apply' (g e : V₀ ≃ₗ[ZMod 2] V₀) (v : V₀) :
    (g * e * g⁻¹) (g v) = g (e v) := by
  simp [mul_apply]

private lemma s16c1c_apply_conj (g x : V₀ ≃ₗ[ZMod 2] V₀) (u : V₀) :
    x u = g ((g⁻¹ * x * g) (g⁻¹ u)) := by
  rw [s16c1c_conj_apply]
  simp

private lemma s16c1c_conj_inv_mul (g e : V₀ ≃ₗ[ZMod 2] V₀) :
    g⁻¹ * (g * e * g⁻¹) * g = e := by
  group

private lemma s16c1c_mul_conj_inv (g x : V₀ ≃ₗ[ZMod 2] V₀) :
    g * (g⁻¹ * x * g) * g⁻¹ = x := by
  group

private lemma s16c1c_closure_conj (g : V₀ ≃ₗ[ZMod 2] V₀)
    {E E' : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} (hmem : ∀ x, x ∈ E' ↔ g⁻¹ * x * g ∈ E)
    {v : V₀} (hv : v ∈ AddSubgroup.closure {u : V₀ | ∃ e ∈ E, e ≠ 1 ∧ e u = u}) :
    g v ∈ AddSubgroup.closure {u : V₀ | ∃ x ∈ E', x ≠ 1 ∧ x u = u} := by
  induction hv using AddSubgroup.closure_induction with
  | mem s hs =>
      rcases hs with ⟨e, he, he1, hes⟩
      refine AddSubgroup.subset_closure ⟨g * e * g⁻¹, ?_, ?_, ?_⟩
      · rw [hmem, s16c1c_conj_inv_mul]
        exact he
      · intro h1
        apply he1
        rw [← s16c1c_conj_inv_mul g e, h1]
        simp
      · rw [s16c1c_conj_apply', hes]
  | zero =>
      rw [map_zero]
      exact AddSubgroup.zero_mem _
  | add w w' _ _ hw hw' =>
      rw [map_add]
      exact AddSubgroup.add_mem _ hw hw'
  | neg w _ hw =>
      rw [map_neg]
      exact AddSubgroup.neg_mem _ hw

theorem s16c1c_e16Lin_conj {E E' : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} (g : V₀ ≃ₗ[ZMod 2] V₀)
    (hmem : ∀ x, x ∈ E' ↔ g⁻¹ * x * g ∈ E) (hE : s16c1cE16Lin E) : s16c1cE16Lin E' := by
  rcases hE with ⟨z, hz, ℓ, hℓ, hE1, hE2, hE3, hE4, hE5⟩
  refine ⟨g z, ?_, ℓ.comp g.symm.toLinearMap, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hz (g.injective (by simpa using h))
  · intro h
    apply hℓ
    apply LinearMap.ext
    intro v
    have hv : (ℓ.comp g.symm.toLinearMap) (g v) = 0 := by rw [h, LinearMap.zero_apply]
    simpa [LinearMap.comp_apply] using hv
  · intro u
    constructor
    · intro hu
      have hfix : ∀ e ∈ E, e (g⁻¹ u) = g⁻¹ u := by
        intro e he
        have hx : g * e * g⁻¹ ∈ E' := by
          rw [hmem, s16c1c_conj_inv_mul]
          exact he
        have h1 : (g * e * g⁻¹) u = u := hu (g * e * g⁻¹) hx
        have h2 : g⁻¹ ((g * e * g⁻¹) u) = g⁻¹ u := congrArg (⇑g⁻¹) h1
        rw [← s16c1c_conj_apply g (g * e * g⁻¹) u, s16c1c_conj_inv_mul] at h2
        exact h2
      rcases (hE1 (g⁻¹ u)).mp hfix with h | h
      · left
        simpa using congrArg (⇑g) h
      · right
        simpa using congrArg (⇑g) h
    · intro hu x hx
      have he : g⁻¹ * x * g ∈ E := (hmem x).mp hx
      have hgu : g⁻¹ u = 0 ∨ g⁻¹ u = z := by
        rcases hu with rfl | h
        · left; simp
        · right; rw [h]; simp
      have hfix : (g⁻¹ * x * g) (g⁻¹ u) = g⁻¹ u := (hE1 (g⁻¹ u)).mpr hgu _ he
      calc x u = g ((g⁻¹ * x * g) (g⁻¹ u)) := s16c1c_apply_conj g x u
        _ = g (g⁻¹ u) := by rw [hfix]
        _ = u := by simp
  · intro x hx u hu
    have he : g⁻¹ * x * g ∈ E := (hmem x).mp hx
    have hlu : ℓ (g⁻¹ u) = 0 := by simpa [LinearMap.comp_apply] using hu
    rcases hE2 (g⁻¹ * x * g) he (g⁻¹ u) hlu with h | h
    · left
      calc x u = g ((g⁻¹ * x * g) (g⁻¹ u)) := s16c1c_apply_conj g x u
        _ = g (g⁻¹ u) := by rw [h]
        _ = u := by simp
    · right
      calc x u = g ((g⁻¹ * x * g) (g⁻¹ u)) := s16c1c_apply_conj g x u
        _ = g (g⁻¹ u + z) := by rw [h]
        _ = g (g⁻¹ u) + g z := by rw [map_add]
        _ = u + g z := by simp
  · intro x hx hx1 u hu
    have he : g⁻¹ * x * g ∈ E := (hmem x).mp hx
    have he1 : g⁻¹ * x * g ≠ 1 := by
      intro h
      apply hx1
      rw [← s16c1c_mul_conj_inv g x, h]
      simp
    have hdisj : (g⁻¹ * x * g) (g⁻¹ u) = g⁻¹ u ∨
        (g⁻¹ * x * g) (g⁻¹ u) = g⁻¹ u + z := by
      rcases hu with h | h
      · left
        calc (g⁻¹ * x * g) (g⁻¹ u) = g⁻¹ (x u) := s16c1c_conj_apply g x u
          _ = g⁻¹ u := by rw [h]
      · right
        calc (g⁻¹ * x * g) (g⁻¹ u) = g⁻¹ (x u) := s16c1c_conj_apply g x u
          _ = g⁻¹ (u + g z) := by rw [h]
          _ = g⁻¹ u + g⁻¹ (g z) := by rw [map_add]
          _ = g⁻¹ u + z := by simp
    simpa [LinearMap.comp_apply] using
      hE3 (g⁻¹ * x * g) he he1 (g⁻¹ u) hdisj
  · intro u hu
    have hlu : ℓ (g⁻¹ u) = 0 := by simpa [LinearMap.comp_apply] using hu
    have hv := s16c1c_closure_conj g hmem (hE4 (g⁻¹ u) hlu)
    simpa using hv
  · obtain ⟨e, he, u₀, hu₀, hne⟩ := hE5
    refine ⟨g * e * g⁻¹, ?_, g u₀, ?_, ?_⟩
    · rw [hmem, s16c1c_conj_inv_mul]
      exact he
    · show ℓ (g⁻¹ (g u₀)) = 0
      simpa [LinearMap.comp_apply] using hu₀
    · intro hh
      apply hne
      have hh' := congrArg (⇑g⁻¹) hh
      simpa [s16c1c_conj_apply'] using hh'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
