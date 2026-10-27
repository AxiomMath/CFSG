module

public import CFSG.LocalAnalysis.StandardType.GGQ2ActualFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.StandardType.GGQ2Frame.CoverComponents

open CFSG CFSG.Assembly CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {G : Type} [Group G] {H A : Subgroup G} {R : Type} [Group R]

@[expose] def Equivariant (hAN : A ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* R) (ρ : ↥A →* R) :
    Prop :=
  ∀ (a : ↥A) (h : ↥H), π (H.normalizerMonoidHom ⟨(a : G), hAN a.2⟩ h) = ρ a * π h * (ρ a)⁻¹

end

end CFSG.StandardType.GGQ2Frame.CoverComponents
