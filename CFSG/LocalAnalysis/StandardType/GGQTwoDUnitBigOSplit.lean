module

public import CFSG.ClassicalGroups.Orthogonal.RootGroupExt
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

import CFSG.LinearAlgebra.RestrictEquiv
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.ClassicalGroups.Orthogonal.RootGroupChar
public import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer
public import CFSG.LocalAnalysis.SectionRank.SignLines

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.ClassicalGroups.Orthogonal (extEquiv)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

abbrev qtwoDB43_perp (Q : QuadraticForm (ZMod 2) V) (V₀ : Submodule (ZMod 2) V) :
    Submodule (ZMod 2) V :=
  LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) V₀

theorem qtwoDB43_isCompl_perp {Q : QuadraticForm (ZMod 2) V} {V₀ : Submodule (ZMod 2) V}
    (hV₀nd : ∀ x ∈ V₀, (∀ y ∈ V₀, QuadraticMap.polar Q x y = 0) → x = 0) :
    IsCompl V₀ (qtwoDB43_perp Q V₀) := by
  have hrefl : (QuadraticMap.polarBilin Q).IsRefl := by
    intro x y hxy
    rw [QuadraticMap.polarBilin_apply_apply] at hxy ⊢
    rwa [QuadraticMap.polar_comm Q]
  have hB : (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) V₀).Nondegenerate := by
    have := CFSG.ClassicalGroups.Orthogonal.nondegenerate_polarBilin_restrict (Q := Q) hV₀nd
    simpa [LinearMap.BilinForm.restrict] using this
  exact LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hB

theorem qtwoDB43_perp_nondegenerate {Q : QuadraticForm (ZMod 2) V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {V₀ : Submodule (ZMod 2) V}
    (hV₀nd : ∀ x ∈ V₀, (∀ y ∈ V₀, QuadraticMap.polar Q x y = 0) → x = 0) :
    (QuadraticMap.polarBilin (Q.restrict (qtwoDB43_perp Q V₀))).Nondegenerate := by
  apply CFSG.ClassicalGroups.Orthogonal.nondegenerate_polarBilin_restrict
  intro x hx horth
  have hxorth : ∀ a ∈ V₀, QuadraticMap.polar Q a x = 0 := by
    intro a ha
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) a ha
    rwa [QuadraticMap.polarBilin_apply_apply] at h
  refine CFSG.ClassicalGroups.Orthogonal.eq_zero_of_polar_eq_zero hQ fun u => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    CFSG.ClassicalGroups.exists_add_eq (qtwoDB43_isCompl_perp hV₀nd) u
  rw [QuadraticMap.polar_add_right, horth b hb, add_zero, QuadraticMap.polar_comm Q]
  exact hxorth a ha

theorem qtwoDB43_ext_injective {V₀ W : Submodule (ZMod 2) V} (hPW : IsCompl V₀ W) :
    Function.Injective (extEquiv hPW) := by
  have hcoe : ∀ (g : W ≃ₗ[ZMod 2] W) (w : W), extEquiv hPW g (w : V) = (g w : V) := by
    intro g w
    simpa using CFSG.ClassicalGroups.Orthogonal.extEquiv_add hPW g (V₀.zero_mem) w.2
  intro g g' h
  refine LinearEquiv.ext fun w => Subtype.ext ?_
  have h1 : (extEquiv hPW g (w : V)) = (extEquiv hPW g' (w : V)) := by rw [h]
  rwa [hcoe g w, hcoe g' w] at h1

theorem qtwoDB43_ext_mem_orthogonalGroup {Q : QuadraticForm (ZMod 2) V}
    {V₀ : Submodule (ZMod 2) V} (hPW : IsCompl V₀ (qtwoDB43_perp Q V₀))
    {g : ↥(qtwoDB43_perp Q V₀) ≃ₗ[ZMod 2] ↥(qtwoDB43_perp Q V₀)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (qtwoDB43_perp Q V₀))) :
    extEquiv hPW g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  obtain ⟨p, hp, w, hw, rfl⟩ := CFSG.ClassicalGroups.exists_add_eq hPW v
  rw [CFSG.ClassicalGroups.Orthogonal.extEquiv_add hPW g hp hw]
  have hgapp := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg) ⟨w, hw⟩
  have hQw : Q ((g ⟨w, hw⟩ : ↥(qtwoDB43_perp Q V₀)) : V) = Q w := by
    simpa [QuadraticMap.restrict_apply] using hgapp
  have hpw : QuadraticMap.polar Q p ((g ⟨w, hw⟩ : ↥(qtwoDB43_perp Q V₀)) : V) = 0 := by
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp (g ⟨w, hw⟩).2) p hp
    rwa [QuadraticMap.polarBilin_apply_apply] at h
  have hpw0 : QuadraticMap.polar Q p w = 0 := by
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hw) p hp
    rwa [QuadraticMap.polarBilin_apply_apply] at h
  have hQv : Q (p + ((g ⟨w, hw⟩ : ↥(qtwoDB43_perp Q V₀)) : V)) =
      Q p + Q ((g ⟨w, hw⟩ : ↥(qtwoDB43_perp Q V₀)) : V) +
        QuadraticMap.polar Q p ((g ⟨w, hw⟩ : ↥(qtwoDB43_perp Q V₀)) : V) :=
    QuadraticMap.map_add Q p ((g ⟨w, hw⟩ : ↥(qtwoDB43_perp Q V₀)) : V)
  have hQwv : Q (p + w) = Q p + Q w + QuadraticMap.polar Q p w :=
    QuadraticMap.map_add Q p w
  rw [hQv, hQwv, hQw, hpw, hpw0, add_zero]

theorem qtwoDB43_factor_through_ext {Q : QuadraticForm (ZMod 2) V}
    {V₀ : Submodule (ZMod 2) V}
    (hV₀nd : ∀ x ∈ V₀, (∀ y ∈ V₀, QuadraticMap.polar Q x y = 0) → x = 0)
    {Γ : Type*} [Group Γ] (ρ : Γ →* (V ≃ₗ[ZMod 2] V))
    (hρ : ∀ γ, ρ γ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hfix : ∀ γ, ∀ x ∈ V₀, ρ γ x = x) :
    ∃ ρ' : Γ →* (↥(qtwoDB43_perp Q V₀) ≃ₗ[ZMod 2] ↥(qtwoDB43_perp Q V₀)),
      (∀ γ, ρ' γ ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (qtwoDB43_perp Q V₀))) ∧
      ∀ γ, extEquiv (qtwoDB43_isCompl_perp hV₀nd) (ρ' γ) = ρ γ := by
  let W := qtwoDB43_perp Q V₀
  let hPW := qtwoDB43_isCompl_perp hV₀nd
  have hPres : ∀ γ, ∀ w ∈ W, ρ γ w ∈ W := by
    intro γ w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    rw [QuadraticMap.polarBilin_apply_apply]
    have hxw : QuadraticMap.polar Q x w = 0 := by
      have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hw) x hx
      rwa [QuadraticMap.polarBilin_apply_apply] at h
    have hxw' : QuadraticMap.polar Q (ρ γ x) (ρ γ w) = 0 := by
      rw [CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem (hρ γ) x w]
      exact hxw
    rwa [hfix γ x hx] at hxw'
  let ρ' : Γ →* (W ≃ₗ[ZMod 2] W) :=
    { toFun := fun γ => CFSG.LinearAlgebra.restrictEquiv (hPres γ)
      map_one' := by
        refine LinearEquiv.ext fun w => Subtype.ext ?_
        simp [CFSG.LinearAlgebra.restrictEquiv_apply]
      map_mul' := by
        intro γ δ
        refine LinearEquiv.ext fun w => Subtype.ext ?_
        simp [CFSG.LinearAlgebra.restrictEquiv_apply, map_mul, LinearEquiv.mul_apply] }
  have hρ'coe : ∀ (γ : Γ) (w : W), ((ρ' γ) w : V) = ρ γ w := by
    intro γ w
    change (CFSG.LinearAlgebra.restrictEquiv (hPres γ) w : V) = ρ γ w
    rw [CFSG.LinearAlgebra.restrictEquiv_apply]
  refine ⟨ρ', fun γ => ?_, fun γ => ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro m
    rw [QuadraticMap.restrict_apply, QuadraticMap.restrict_apply, hρ'coe γ m]
    exact CFSG.ClassicalGroups.Orthogonal.map_of_mem (hρ γ) (m : V)
  · change extEquiv hPW (ρ' γ) = ρ γ
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨p, hp, w, hw, rfl⟩ := CFSG.ClassicalGroups.exists_add_eq hPW v
    rw [CFSG.ClassicalGroups.Orthogonal.extEquiv_add hPW (ρ' γ) hp hw,
      map_add (ρ γ), hfix γ p hp]
    congr 1

end CFSG.StandardType.QTwo

end
