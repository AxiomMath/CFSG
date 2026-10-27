module

public import CFSG.Quasithin.AppendixH.H16.ConjNat
public import CFSG.Quasithin.Background.HLUCode24

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.LU24
  CFSG.Monster.Code

private lemma congrHom_eq_mul_inv (e x : MulAut W11) :
    CFSG.Quasithin.H.congrHom e x = e * x * e⁻¹ := by
  ext w
  simp only [CFSG.Quasithin.H.congrHom_apply, MulAut.mul_apply, MulAut.inv_apply]

theorem imgCd_conjSubg {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm)
    {A : Subgroup (Equiv.Perm (Fin 24))} (hA : A ≤ AutPerm) :
    imgCd (conjSubg σ A) = (imgCd A).map (CFSG.Quasithin.H.congrHom (rhoCd hσ)) := by
  let ρ₀ : ↥AutPerm →* MulAut W11 := rhoC11 AutPerm le_rfl
  let σ' : ↥AutPerm := ⟨σ, hσ⟩
  have hmain : ∀ γ : ↥AutPerm,
      CFSG.Quasithin.H.congrHom (rhoCd hσ) (ρ₀ γ) = ρ₀ ((σ'⁻¹)⁻¹ * γ * σ'⁻¹) := by
    intro γ
    have he : (rhoCd hσ : MulAut W11) = ρ₀ σ' := rfl
    calc CFSG.Quasithin.H.congrHom (rhoCd hσ) (ρ₀ γ)
        = (rhoCd hσ) * (ρ₀ γ) * (rhoCd hσ)⁻¹ := congrHom_eq_mul_inv _ _
      _ = ρ₀ σ' * ρ₀ γ * (ρ₀ σ')⁻¹ := by rw [he]
      _ = ρ₀ (σ' * γ * σ'⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = ρ₀ ((σ'⁻¹)⁻¹ * γ * σ'⁻¹) := by rw [inv_inv]
  have key := map_congrHom_rImg ρ₀ ρ₀ (rhoCd hσ) (σ'⁻¹) hmain (A := A) hA
  have hσ'inv : (((σ'⁻¹ : ↥AutPerm) : S24))⁻¹ = σ := by simp [σ']
  show rImg ρ₀ (conjSubg σ A) = (rImg ρ₀ A).map (CFSG.Quasithin.H.congrHom (rhoCd hσ))
  rw [key, hσ'inv]

theorem fixV_imgCd_conjSubg {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm)
    {A : Subgroup (Equiv.Perm (Fin 24))} (hA : A ≤ AutPerm) :
    fixV (imgCd (conjSubg σ A)) = (fixV (imgCd A)).map (rhoCd hσ).toMonoidHom := by
  rw [imgCd_conjSubg hσ hA, CFSG.Quasithin.H.fixV_map_congrHom]

end CFSG.ASVolI.H16
