module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.PrimeChar
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompStabilizer

public section

namespace Certificates

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg in
theorem certificate13723 : ∀ χ : Multiplicative (Fin Tag.E7.rank → ℤ) →* Zp 5, charStabilizer χ = kernelWeylGroup χ :=
  CFSG.HardMathSupport.Timmesfeld.CrossChar.charStabilizer_eq_kernelWeylGroup_E7_five_affine

end Certificates
