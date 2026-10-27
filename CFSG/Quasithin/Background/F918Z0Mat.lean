module

public import CFSG.Quasithin.Background.F918Z0AuxLin

public section

namespace CFSG.Quasithin

theorem hasMatModel_of_irr {V : Type} [CommGroup V] [Finite V] [Nontrivial V]
    (hexp : ∀ v : V, v ^ 2 = 1) {D X : Subgroup (MulAut V)}
    (hcomm : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g)
    (hirr : ∀ U : Subgroup V, (∀ g ∈ D ⊔ X, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    HasMatModel D X := by
  obtain ⟨F, _, _, _, I, _, _, _, _, r, hr, Φ, ρI, σ, h⟩ :=
    MatModel.exists_isDecomp hexp hcomm hirr
  exact MatModel.hasMatModel_of_isDecomp hr h hirr

end CFSG.Quasithin
