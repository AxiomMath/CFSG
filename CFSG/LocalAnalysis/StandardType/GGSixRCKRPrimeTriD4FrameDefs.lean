module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LocalAnalysis.StandardType.GGFinModelRat
public import CFSG.LieType.Steinberg.TwistedD4.Defs

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.GGFinModel
open CFSG.LieType.Steinberg.TwistedD4 (nd)

@[expose] noncomputable def triPsi (h r : ℕ) : ModGL Tag.D4 GGL →* ModGL Tag.D4 GGL :=
  (MulAut.conj ((diagramMap TwistTag.D4 GGL : ModGL Tag.D4 GGL) ^ r)).toMonoidHom.comp
    (Units.map (entrywiseHom (iterateFrobenius GGL 2 h)))

@[expose] def RCKTriD4Frame
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀)
    (Ψ : Set (Fin τ.rank → ℤ)) (h : ℕ) : Prop :=
  ∃ (r : ℕ) (_ : r = 1 ∨ r = 2) (hY : ∀ y ∈ rootSpan τ GGL Ψ, S.D.step y ∈ rootSpan τ GGL Ψ)
    (Ξ : ↥(rootSpan τ GGL Ψ) ≃* ↥(adjointGroup Tag.D4 GGL)),
    (∀ (y : ModGL τ GGL) (hy : y ∈ rootSpan τ GGL Ψ),
      (Ξ ⟨S.D.step y, hY y hy⟩ : ModGL Tag.D4 GGL) = triPsi h r (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL)) ∧
    ∃ z ∈ rootSpan τ GGL Ψ, ∃ γ ∈ Ψ,
      (∀ y, y ∈ (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom ↔
        ∃ hy : y ∈ rootSpan τ GGL Ψ,
          (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) ∈ rootSubgroup Tag.D4 GGL (Pi.single (nd 2) 1)) ∧
      (∀ y, y ∈ (rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom ↔
        ∃ hy : y ∈ rootSpan τ GGL Ψ,
          (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) ∈ rootSubgroup Tag.D4 GGL (-Pi.single (nd 2) 1))

end CFSG.StandardType.RCKRP

end
