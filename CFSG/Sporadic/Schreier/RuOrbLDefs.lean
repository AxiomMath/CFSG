module

public import CFSG.Sporadic.Schreier.RuTreeEltA

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def ruReps : List ℕ :=
  [0, 2, 3, 7, 8, 10, 13, 15, 20, 24, 26, 27, 30, 75, 92, 108, 153, 204, 1046]

@[expose] def ruRepZA (k : ℕ) : Array ℕ := ruTZA (ruReps.getD k 0)

end CFSG.Sporadic.RuSchreier
