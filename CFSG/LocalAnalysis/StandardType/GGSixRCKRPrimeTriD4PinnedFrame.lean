module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4FrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnedFrame

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
open CFSG.LieType.Steinberg.TwistedD4 (nd)

@[expose] def RCKTriD4PinnedFrameAt
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) (Ψ : Set (Fin τ.rank → ℤ)) (h r : ℕ)
    (m : ModGL Tag.D4 GGL) : Prop :=
  ∃ (hY : ∀ y ∈ rootSpan τ GGL Ψ, S.D.step y ∈ rootSpan τ GGL Ψ)
    (Ξ : ↥(rootSpan τ GGL Ψ) ≃* ↥(adjointGroup Tag.D4 GGL))
    (ι : (Fin τ.rank → ℤ) →+ (Fin Tag.D4.rank → ℤ)),
    (∀ (y : ModGL τ GGL) (hy : y ∈ rootSpan τ GGL Ψ),
      (Ξ ⟨S.D.step y, hY y hy⟩ : ModGL Tag.D4 GGL) =
        m * triPsi h r (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) * m⁻¹) ∧
    Set.BijOn ι Ψ {δ | IsRoot Tag.D4 δ} ∧
    (∀ γ ∈ Ψ, ∀ δ ∈ Ψ, CFSG.LieType.Steinberg.Adjoint.iform (ι γ) (ι δ) =
      CFSG.LieType.Steinberg.Adjoint.iform γ δ) ∧
    (∀ γ ∈ Ψ, ∀ (y : ModGL τ GGL) (hy : y ∈ rootSpan τ GGL Ψ),
      y ∈ rootSubgroup τ GGL γ ↔
        (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) ∈ rootSubgroup Tag.D4 GGL (ι γ)) ∧
    ∀ b ∈ torusGroup τ GGL, ∃ t ∈ torusGroup Tag.D4 GGL,
      (∀ (y : ModGL τ GGL) (hy : y ∈ rootSpan τ GGL Ψ) (hby : b * y * b⁻¹ ∈ rootSpan τ GGL Ψ),
        (Ξ ⟨b * y * b⁻¹, hby⟩ : ModGL Tag.D4 GGL) = t * (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) * t⁻¹) ∧
      ∀ γ ∈ Ψ, rckRootVal t (ι γ) = rckRootVal b γ

@[expose] def RCKTriD4PinnedFrame
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) (Ψ : Set (Fin τ.rank → ℤ)) (h : ℕ) : Prop :=
  ∃ (r : ℕ) (m : ModGL Tag.D4 GGL), (r = 1 ∨ r = 2) ∧ m ∈ monomialSubgroup Tag.D4 GGL ∧
    m ∈ adjointGroup Tag.D4 GGL ∧ RCKTriD4PinnedFrameAt S Ψ h r m

@[expose] def RCKTriD4Model
    (h : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F), TriField F σ h ∧
    ∃ (ιA : (triD4Universal F σ).K →* ModGL Tag.D4 GGL)
      (β₀ : Fin (triD4Universal F σ).D.rank → ℤ),
      Function.Injective ιA ∧
      ιA.range = adjointGroup Tag.D4 GGL ⊓ (triPsi h 1).eqLocus (MonoidHom.id _) ∧
      β₀ ∈ (triD4Universal F σ).D.roots ∧ GGLongRoot (triD4Universal F σ).D β₀ ∧
      ((triD4Universal F σ).D.rootGroup β₀).map ιA =
        rootSubgroup Tag.D4 GGL (Pi.single (nd 2) 1) ⊓ (triPsi h 1).eqLocus (MonoidHom.id _) ∧
      ((triD4Universal F σ).D.rootGroup (-β₀)).map ιA =
        rootSubgroup Tag.D4 GGL (-Pi.single (nd 2) 1) ⊓ (triPsi h 1).eqLocus (MonoidHom.id _)

end CFSG.StandardType.RCKRP

end
