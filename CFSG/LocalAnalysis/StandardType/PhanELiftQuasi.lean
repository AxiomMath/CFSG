module

public import CFSG.LieType.Universal.Catalog
import CFSG.LieType.CurtisTits.TwistedE6
import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
import CFSG.LieType.Steinberg.Adjoint.Perfect

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal


theorem isQuasisimple_lieUniversal_twistedE6 (f : ℕ) (hf : 1 ≤ f) :
    CFSG.IsQuasisimple (lieUniversal .twistedE6 0 2 f Nat.prime_two).K :=
  CFSG.LieType.CurtisTits.isQuasisimple_twistedE6 2 f hf

theorem isQuasisimple_lieUniversal_E7 (f : ℕ) :
    CFSG.IsQuasisimple (lieUniversal .E7 0 2 f Nat.prime_two).K :=
  CFSG.LieType.CurtisTits.isQuasisimple_e7 (GaloisField 2 f)

theorem isQuasisimple_lieUniversal_E8
    (f : ℕ) :
    CFSG.IsQuasisimple (lieUniversal .E8 0 2 f Nat.prime_two).K :=
  CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 (GaloisField 2 f)

end CFSG.ClassicalInvolution.Phan.PhanE
