module

public import CFSG.GF2Type.Smith1979.IdxFourModelDefs
import Certificates.Kernel.IdxFour.M0Coset

public section

namespace Certificates

open CFSG.GF2Type.Smith1979.IdxFour in
theorem certificate17600 : Nat.card M0 = 39191040 :=
  CFSG.KD.IF4M.card_M0

end Certificates
