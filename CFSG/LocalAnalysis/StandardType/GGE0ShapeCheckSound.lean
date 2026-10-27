module

public import Certificates.Certificate716800
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem shapeCheck_sound
    (b₀ b₁ : Fin Tag.E6.rank → ZMod 3)
    (hind : ∀ c₀ c₁ : ZMod 3, c₀ • b₀ + c₁ • b₁ = 0 → c₀ = 0 ∧ c₁ = 0)
    (hlarge : 6 < {γ | IsRoot .E6 γ ∧ triPairing b₀ γ = 0 ∧ triPairing b₁ γ = 0}.ncard)
    {w : WeylGroup .E6} (h₀ : w ∈ charStabilizer (triChar b₀))
    (h₁ : w ∈ charStabilizer (triChar b₁)) :
    triPairing b₀ (e6Shift w) = 0 ∧ triPairing b₁ (e6Shift w) = 0 :=
  Certificates.certificate716800 b₀ b₁ hind hlarge w h₀ h₁

end CFSG.StandardType
