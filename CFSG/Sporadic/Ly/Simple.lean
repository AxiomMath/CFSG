
module

public import CFSG.Sporadic.Ly.SimpleBase

public import CFSG.Sporadic.Ly.Action

public section

namespace CFSG.Sporadic.Ly

open CFSG.Sporadic.LySchreier MulAction

theorem stabilizer_root : stabilizer J root = lyH :=
  stabilizer_zero

theorem card_stabilizer_root :
    Nat.card (stabilizer J root) = 5859000000 := by
  rw [stabilizer_root]
  exact ly_certificate.2.2.2.1

end CFSG.Sporadic.Ly
