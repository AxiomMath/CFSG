module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open Equiv

theorem perm_fin5_eq_one (π : Perm (Fin 5)) (h0 : π 0 = 0)
    (h1 : π * (swap 1 2 * swap 2 3) = (swap 1 2 * swap 2 3) * π)
    (h2 : π * (swap 1 2 * swap 2 4) = (swap 1 2 * swap 2 4) * π) : π = 1 := by
  revert π
  decide +kernel

theorem sign_threeCycle_fin5 (a b c : Fin 5) (hab : a ≠ b) (hbc : b ≠ c) :
    Perm.sign (swap a b * swap b c) = 1 := by
  rw [Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hbc]
  rfl

theorem perm_eq_one_of_commute_alt {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hΩ : Fintype.card Ω = 5) (ω₀ : Ω) (π : Perm Ω) (hπ : π ω₀ = ω₀)
    (h : ∀ w : Perm Ω, w ∈ alternatingGroup Ω → w ω₀ = ω₀ → π * w = w * π) : π = 1 := by
  have e0 : Ω ≃ Fin 5 := Fintype.equivFinOfCardEq hΩ
  let e : Ω ≃ Fin 5 := e0.trans (swap (e0 ω₀) 0)
  have he : e ω₀ = 0 := by simp [e]
  let σ₁ : Perm (Fin 5) := swap 1 2 * swap 2 3
  let σ₂ : Perm (Fin 5) := swap 1 2 * swap 2 4
  have hsym : e.symm 0 = ω₀ := by rw [Equiv.symm_apply_eq]; exact he.symm
  have hcomm : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → σ 0 = 0 →
      e.permCongrHom π * σ = σ * e.permCongrHom π := by
    intro σ hs h0
    set w : Perm Ω := e.permCongrHom.symm σ with hwdef
    have hww : e.permCongrHom w = σ := e.permCongrHom.apply_symm_apply σ
    have hw : w ∈ alternatingGroup Ω := by
      rw [Perm.mem_alternatingGroup]
      have := Perm.sign_permCongr e w
      have h' : Perm.sign (e.permCongrHom w) = Perm.sign w := this
      rw [← h', hww]
      exact hs
    have hw0 : w ω₀ = ω₀ := by
      have h1 : e.permCongrHom w (e ω₀) = e (w ω₀) := by
        show (e.permCongr w) (e ω₀) = e (w ω₀)
        simp [Equiv.permCongr_apply]
      rw [hww, he, h0] at h1
      apply e.injective
      rw [he]
      exact h1.symm
    have := h w hw hw0
    have h3 := congrArg e.permCongrHom this
    rwa [map_mul, map_mul, hww] at h3
  have hfix : e.permCongrHom π 0 = 0 := by
    show (e.permCongr π) 0 = 0
    simp [Equiv.permCongr_apply, hsym, hπ, he]
  have h1 := hcomm σ₁ (sign_threeCycle_fin5 1 2 3 (by decide) (by decide)) (by decide)
  have h2 := hcomm σ₂ (sign_threeCycle_fin5 1 2 4 (by decide) (by decide)) (by decide)
  have := perm_fin5_eq_one _ hfix h1 h2
  exact e.permCongrHom.injective (this.trans (map_one e.permCongrHom).symm)

end CFSG.Quasithin.Background.Harris.KFact2d
