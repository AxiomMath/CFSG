module

public import CFSG.Sporadic.Th.Recog.EightP

public section

local instance (priority := high) : AddCommGroup (ZMod 2) :=
  Ring.toAddCommGroup

namespace CFSG.Sporadic.Th.Recog

open CFSG

variable {G : Type} [Group G] [Finite G]

theorem exists_iso_rho8a (S : ThSetting G) (hBB : A9FaithfulDimEight) :
    ∃ (σ : Equiv.Perm (Fin 9)) (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8),
      ∀ g v, e (S.rho g v) = rho8a (conjA σ g) (e v) := by
  obtain ⟨σ, e, he | he⟩ :=
    hBB S.toSetting.Qt S.finrank_Qt S.rho S.rho_injective
  · exact ⟨σ, e, he⟩
  · exact (not_rho8p S e he).elim

theorem q_eq_qf (S : ThSetting G) {σ : Equiv.Perm (Fin 9)} {e : S.toSetting.Qt ≃ₗ[ZMod 2] V8}
    (he : ∀ g v, e (S.rho g v) = rho8a (conjA σ g) (e v)) (v : S.toSetting.Qt) :
    S.toSetting.q v = qf (e v) := by
  classical
  let Q' : QuadraticForm (ZMod 2) V8 :=
    QuadraticMap.comp S.toSetting.q e.symm.toLinearMap
  have hQ' : ∀ v, Q' v = S.toSetting.q (e.symm v) := fun _ => rfl
  have hcongr : QuadraticMap.polarBilin Q' =
      (LinearMap.BilinForm.congr e) (QuadraticMap.polarBilin S.toSetting.q) := by
    apply LinearMap.BilinForm.ext
    intro x y
    rw [LinearMap.BilinForm.congr_apply, QuadraticMap.polarBilin_comp,
      LinearMap.compl₁₂_apply]
    rfl
  have hndB : LinearMap.BilinForm.Nondegenerate (QuadraticMap.polarBilin Q') := by
    rw [hcongr]
    exact LinearMap.BilinForm.Nondegenerate.congr e S.toSetting.q_nondegenerate
  have hrho_q : ∀ (g : alternatingGroup (Fin 9)) (x : S.toSetting.Qt),
      S.toSetting.q (S.rho g x) = S.toSetting.q x := by
    intro g x
    obtain ⟨h, rfl⟩ := S.θ_surj g
    rw [S.rho_θ h]
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
      (S.toSetting.ρ (S.toSettingE h)).property x
  have hinv : ∀ g v, Q' (rho8a g v) = Q' v := by
    intro g v
    obtain ⟨g₀, rfl⟩ := (conjA σ).surjective g
    rw [hQ', hQ']
    have h1 : e.symm (rho8a (conjA σ g₀) v) = S.rho g₀ (e.symm v) := by
      have h := he g₀ (e.symm v)
      simp only [LinearEquiv.apply_symm_apply] at h
      rw [← h, LinearEquiv.symm_apply_apply]
    rw [h1]
    exact hrho_q g₀ (e.symm v)
  have hnd : ∀ v : V8, v ≠ 0 → ∃ w : V8, QuadraticMap.polar Q' v w ≠ 0 := by
    intro v hv
    by_contra h
    have hzero : ∀ w, QuadraticMap.polar Q' v w = 0 := by
      intro w
      by_contra hw
      exact h ⟨w, hw⟩
    have hvzero : v = 0 :=
      hndB.left v (by
        intro w
        rw [QuadraticMap.polarBilin_apply_apply]
        exact hzero w)
    exact hv hvzero
  have h := eq_qf_of_invariant Q' hinv hnd (e v)
  rw [hQ'] at h
  simpa using h

end CFSG.Sporadic.Th.Recog
