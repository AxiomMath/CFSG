module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.PrimeChar
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompStabilizer

public section

namespace Certificates

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg in
theorem certificate13721 : ∀ χ : Multiplicative (Fin Tag.E7.rank → ℤ) →* Zp 7, charStabilizer χ = kernelWeylGroup χ :=
  CFSG.HardMathSupport.Timmesfeld.CrossChar.charStabilizer_eq_kernelWeylGroup_E7_seven_affine

end Certificates
