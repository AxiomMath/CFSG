module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnedFrame

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.GGFinModel

@[expose] def RCKFramePairCore
    : Prop :=
  ∀ (τ : Tag), (τ = Tag.D4 ∨ τ = Tag.E6 ∨ τ = Tag.E7) → ∀ (S : LangSetup τ GGL 5)
    (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∀ z ∈ adjointGroup τ GGL,
    ((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom).map S.D.step =
        (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom →
    ((rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom).map S.D.step =
        (rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom →
    ∀ r ∈ S.D.model, ∃ u ∈ S.Γ,
      u⁻¹ * r ∈ Subgroup.normalizer ((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom) ∧
      u⁻¹ * r ∈ Subgroup.normalizer ((rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom)

end CFSG.StandardType.RCKRP
