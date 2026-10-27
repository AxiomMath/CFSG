module

public import CFSG.Sporadic.Bridge.BData

public section

namespace CFSG.Sporadic.Bridge.B

open CFSG.Monster.B.Bin CFSG.Monster.B.Primes.Native

set_option compiler.extract_closed false

@[expose] def tcHR : List (List Nat) := [[0, 1, 0, 0], [3, 1, 1, 0], [2, 2, 2, 0], [1, 1, 1, 4]]

@[expose] def tcHC : List Nat := [0, 1, 2, 2]

end CFSG.Sporadic.Bridge.B
