
module

public import CFSG.GF2Type.Smith1979.IdxFourModelBasic
import Certificates.Kernel.IdxFour.X0Cent

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.IdxFour in
theorem certificate17604 : Nat.card ↥(M0 ⊓ Subgroup.centralizer ({s12e} : Set (V12 ≃ₗ[ZMod 2] V12))) = 311040 :=
  CFSG.KD.IF4X.card_centralizer_s12e

end Certificates
