module

public import CFSG.Quasithin.Background.F918Z2SwapData
public import CFSG.Quasithin.Background.F918Z0Mat

public section

namespace CFSG.Quasithin

open scoped Matrix

theorem hasSqModel_swap_form {V : Type} [CommGroup V] [Finite V] [Nontrivial V]
    (hexp : ∀ v : V, v ^ 2 = 1) {D X : Subgroup (MulAut V)}
    (hcomm : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g)
    (hirr : ∀ U : Subgroup V, (∀ g ∈ D ⊔ X, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {s : MulAut V} (hDX : X = D.map (MulAut.conj s).toMonoidHom)
    (hXD : D = X.map (MulAut.conj s).toMonoidHom) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (d : ℕ)
      (β : V ≃* Multiplicative (Matrix (Fin d) (Fin d) F))
      (ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F)
      (σ : ↥X →* Matrix.GeneralLinearGroup (Fin d) F)
      (ϑ : F ≃+* F) (Q R : Matrix (Fin d) (Fin d) F),
      0 < d ∧ IsMatModel D X β ρ σ ∧ IsUnit Q ∧ IsUnit R ∧
        ∀ v : V, Multiplicative.toAdd (β (s v)) =
          Q * ((Multiplicative.toAdd (β v)).map ϑ)ᵀ * R := by
  have _ := hXD
  obtain ⟨F, _, _, _, d, r, β, ρ, σ, hd, hr, hM⟩ := hasMatModel_of_irr hexp hcomm hirr
  have hrd : r = d := SwapModel.swap_dim_eq hM hd hr hDX
  subst hrd
  obtain ⟨ϑ, Q, R, hQ, hR, hform⟩ := SwapModel.swap_form_of_sqModel hM hd hDX
  exact ⟨F, inferInstance, inferInstance, inferInstance, r, β, ρ, σ, ϑ, Q, R, hd, hM, hQ, hR,
    hform⟩

end CFSG.Quasithin
