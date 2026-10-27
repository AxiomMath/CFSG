module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45L3Ctx

public section

namespace CFSG.Quasithin.H13.F431.F48Rig

open CFSG.Quasithin CFSG.Quasithin.H13.F431.F45

variable {D X : Type} [Group D] [Group X]

theorem centralizer_inn_trivial (A : LieAmalgamExt D) (hfin : Finite D) (pm : ℕ) (hpm : 3 ≤ pm)
    (hcen : Subgroup.center D = ⊥) (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K)
    (E : D ≃* X) (k : (A.setting hfin pm hpm).ι.G0)
    (hk : ∀ y : X, k * phiG0 A hfin pm hpm (innHom A hgen E) y =
      phiG0 A hfin pm hpm (innHom A hgen E) y * k) : k = 1 := by
  set κ : MulAut D := settingToAut A hfin pm hpm k with hκ
  have hcomm : ∀ d : D, κ * MulAut.conj d = MulAut.conj d * κ := by
    intro d
    have h1 := congrArg (settingToAut A hfin pm hpm) (hk (E d))
    rw [map_mul, map_mul] at h1
    have h2 : settingToAut A hfin pm hpm (phiG0 A hfin pm hpm (innHom A hgen E) (E d)) =
        MulAut.conj d := by
      show ((innHom A hgen E (E d) : ↥A.K) : MulAut D) = _
      rw [innHom_coe, E.symm_apply_apply]
    rw [h2] at h1
    exact h1
  have hfix : ∀ d : D, κ d = d := by
    intro d
    have hz : d⁻¹ * κ d ∈ Subgroup.center D := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨x, rfl⟩ := κ.surjective z
      have h1 := congrArg (fun φ : MulAut D => φ x) (hcomm d)
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at h1
      calc κ x * (d⁻¹ * κ d) = d⁻¹ * (d * κ x * d⁻¹) * κ d := by group
        _ = d⁻¹ * (κ d * κ x * (κ d)⁻¹) * κ d := by rw [h1]
        _ = d⁻¹ * κ d * κ x := by group
    rw [hcen, Subgroup.mem_bot, inv_mul_eq_one] at hz
    exact hz.symm
  have hκ1 : κ = 1 := MulEquiv.ext fun d => by rw [hfix d]; rfl
  exact Subtype.ext (Subtype.ext hκ1)

end CFSG.Quasithin.H13.F431.F48Rig
