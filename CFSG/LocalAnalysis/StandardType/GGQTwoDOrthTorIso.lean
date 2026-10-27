module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorBlockBase
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorBlockMain

public section

namespace CFSG.StandardType.QTwo

open TauCeti.QuadraticMap QuadraticMap CFSG.RankThree.Classical2
open scoped commutatorElement

section Iso

variable {k : Type} [Field k] {V W : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W] {Q : QuadraticForm k V}
  {Q' : QuadraticForm k W} (χ : V ≃ₗ[k] W) (t : V ≃ₗ[k] V)

theorem orthogonalGroup_map_autCongr (hχ : ∀ v, Q' (χ v) = Q v) :
    (orthogonalGroup Q).map (LinearEquiv.autCongr χ).toMonoidHom = orthogonalGroup Q' := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine mem_orthogonalGroup_iff.2 fun w => ?_
    rw [MulEquiv.coe_toMonoidHom, LinearEquiv.autCongr_apply_apply]
    rw [hχ (f (χ.symm w)), map_app_of_mem_orthogonalGroup hf (χ.symm w)]
    rw [← hχ (χ.symm w), χ.apply_symm_apply]
  · intro hg
    refine ⟨(LinearEquiv.autCongr χ).symm g, ?_, MulEquiv.apply_symm_apply _ _⟩
    refine mem_orthogonalGroup_iff.2 fun v => ?_
    rw [LinearEquiv.autCongr_symm_apply_apply]
    rw [← hχ (χ.symm (g (χ v))), χ.apply_symm_apply]
    rw [map_app_of_mem_orthogonalGroup hg (χ v), hχ v]

private lemma plh_mem_torV₀_set (t : V ≃ₗ[k] V) {v : V} :
    v ∈ (torV₀ t : Set V) ↔ t v = v := by
  change v ∈ torV₀ t ↔ t v = v
  rw [torV₀, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
  exact sub_eq_zero

private lemma plh_mem_torV₁_set (t : V ≃ₗ[k] V) {v : V} :
    v ∈ (torV₁ t : Set V) ↔ ∃ z : V, t z - z = v := by
  change v ∈ torV₁ t ↔ ∃ z : V, t z - z = v
  rw [torV₁, LinearMap.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, by simpa [LinearMap.sub_apply, LinearMap.id_apply] using hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by simpa [LinearMap.sub_apply, LinearMap.id_apply] using hz⟩

theorem torV₀_map : (torV₀ t).map (χ : V →ₗ[k] W) = torV₀ (LinearEquiv.autCongr χ t) := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    have htv : t v = v := (plh_mem_torV₀_set t).mp hv
    refine (plh_mem_torV₀_set (LinearEquiv.autCongr χ t)).mpr ?_
    change (LinearEquiv.autCongr χ t) (χ v) = χ v
    rw [LinearEquiv.autCongr_apply_apply]
    change χ (t (χ.symm (χ v))) = χ v
    rw [LinearEquiv.symm_apply_apply, htv]
  · intro hw
    have hw' : (LinearEquiv.autCongr χ t) w = w :=
      (plh_mem_torV₀_set (LinearEquiv.autCongr χ t)).mp hw
    refine ⟨χ.symm w, ?_, χ.apply_symm_apply w⟩
    refine (plh_mem_torV₀_set t).mpr ?_
    have h := congrArg χ.symm hw'
    simpa [LinearEquiv.autCongr_apply_apply] using h

theorem torV₁_map : (torV₁ t).map (χ : V →ₗ[k] W) = torV₁ (LinearEquiv.autCongr χ t) := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨z, hz⟩ := (plh_mem_torV₁_set t).mp hv
    have hz' : t z - z = v := hz
    refine (plh_mem_torV₁_set (LinearEquiv.autCongr χ t)).mpr ⟨χ z, ?_⟩
    change (LinearEquiv.autCongr χ t) (χ z) - χ z = χ v
    rw [LinearEquiv.autCongr_apply_apply]
    change χ (t (χ.symm (χ z))) - χ z = χ v
    rw [LinearEquiv.symm_apply_apply]
    change χ (t z) - χ z = χ v
    rw [← map_sub]
    change χ (t z - z) = χ v
    rw [hz']
  · intro hw
    obtain ⟨y, hy⟩ := (plh_mem_torV₁_set (LinearEquiv.autCongr χ t)).mp hw
    have hy'' : χ (t (χ.symm y)) - y = w := by
      have h : (LinearEquiv.autCongr χ t) y - y = w := by
        simpa [LinearMap.sub_apply, LinearMap.id_apply] using hy
      rw [LinearEquiv.autCongr_apply_apply] at h
      exact h
    refine ⟨t (χ.symm y) - χ.symm y, ?_, ?_⟩
    · exact (plh_mem_torV₁_set t).mpr ⟨χ.symm y, rfl⟩
    · rw [map_sub]
      change χ (t (χ.symm y)) - χ (χ.symm y) = w
      rw [LinearEquiv.apply_symm_apply]
      exact hy''

private lemma plh_torFix_map_autCongr (χ : V ≃ₗ[k] W) (U : Submodule k V) :
    (torFix U).map (LinearEquiv.autCongr χ).toMonoidHom =
      torFix (U.map (χ : V →ₗ[k] W)) := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩ w hw
    obtain ⟨v, hv, rfl⟩ := hw
    change (LinearEquiv.autCongr χ h) (χ v) = χ v
    rw [LinearEquiv.autCongr_apply_apply]
    change χ (h (χ.symm (χ v))) = χ v
    rw [LinearEquiv.symm_apply_apply, hh v hv]
  · intro hg
    refine ⟨(LinearEquiv.autCongr χ).symm g, ?_, MulEquiv.apply_symm_apply _ _⟩
    intro v hv
    rw [LinearEquiv.autCongr_symm_apply_apply]
    change χ.symm (g ((χ : V →ₗ[k] W) v)) = v
    have hfix := hg ((χ : V →ₗ[k] W) v) ⟨v, hv, rfl⟩
    rw [hfix]
    change χ.symm (χ v) = v
    rw [LinearEquiv.symm_apply_apply]

private lemma plh_centralizer_map (χ : V ≃ₗ[k] W) (t : V ≃ₗ[k] V) :
    (Subgroup.centralizer ({t} : Set (V ≃ₗ[k] V))).map
        (LinearEquiv.autCongr χ).toMonoidHom =
      Subgroup.centralizer ({LinearEquiv.autCongr χ t} : Set (W ≃ₗ[k] W)) := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    have hh' : t * h = h * t := (Subgroup.mem_centralizer_iff.mp hh) t (by simp)
    have hc := congrArg (LinearEquiv.autCongr χ) hh'
    simpa [MulEquiv.coe_toMonoidHom] using hc
  · intro hg
    refine ⟨(LinearEquiv.autCongr χ).symm g, ?_, MulEquiv.apply_symm_apply _ _⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    have hg' : LinearEquiv.autCongr χ t * g = g * LinearEquiv.autCongr χ t :=
      (Subgroup.mem_centralizer_iff.mp hg) (LinearEquiv.autCongr χ t) (by simp)
    have hc := congrArg (LinearEquiv.autCongr χ).symm hg'
    simpa [MulEquiv.coe_toMonoidHom] using hc

theorem torE₀_map_autCongr (hχ : ∀ v, Q' (χ v) = Q v) :
    (torE₀ Q t).map (LinearEquiv.autCongr χ).toMonoidHom =
      torE₀ Q' (LinearEquiv.autCongr χ t) := by
  rw [torE₀, torE₀,
    Subgroup.map_inf (orthogonalGroup Q) (torFix (torV₁ t)) (LinearEquiv.autCongr χ).toMonoidHom
      (LinearEquiv.autCongr χ).injective,
    orthogonalGroup_map_autCongr χ hχ, plh_torFix_map_autCongr χ (torV₁ t), torV₁_map χ t]

theorem torE₁_map_autCongr (hχ : ∀ v, Q' (χ v) = Q v) :
    (torE₁ Q t).map (LinearEquiv.autCongr χ).toMonoidHom =
      torE₁ Q' (LinearEquiv.autCongr χ t) := by
  rw [torE₁, torE₁,
    Subgroup.map_inf (orthogonalGroup Q ⊓ torFix (torV₀ t))
      (Subgroup.centralizer ({t} : Set (V ≃ₗ[k] V))) (LinearEquiv.autCongr χ).toMonoidHom
      (LinearEquiv.autCongr χ).injective,
    Subgroup.map_inf (orthogonalGroup Q) (torFix (torV₀ t)) (LinearEquiv.autCongr χ).toMonoidHom
      (LinearEquiv.autCongr χ).injective,
    orthogonalGroup_map_autCongr χ hχ, plh_torFix_map_autCongr χ (torV₀ t), torV₀_map χ t,
    plh_centralizer_map χ t]

theorem torP₀_map_autCongr (hχ : ∀ v, Q' (χ v) = Q v) :
    (torP₀ Q t).map (LinearEquiv.autCongr χ).toMonoidHom =
      torP₀ Q' (LinearEquiv.autCongr χ t) := by
  rw [torP₀, torP₀, Subgroup.map_commutator, torE₀_map_autCongr χ t hχ]

theorem torP₁_map_autCongr (hχ : ∀ v, Q' (χ v) = Q v) :
    (torP₁ Q t).map (LinearEquiv.autCongr χ).toMonoidHom =
      torP₁ Q' (LinearEquiv.autCongr χ t) := by
  rw [torP₁, torP₁, Subgroup.map_commutator, torE₁_map_autCongr χ t hχ]

end Iso

end CFSG.StandardType.QTwo

end
