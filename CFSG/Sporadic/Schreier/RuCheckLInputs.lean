module

public import CFSG.Sporadic.Schreier.RuCheckChains
public import CFSG.Sporadic.Schreier.RuWitArrays
public meta import CFSG.Sporadic.Schreier.RuCheckChains
public meta import CFSG.Sporadic.Schreier.RuWitArrays

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def ruVpA (p : ℕ) : Array ℕ :=
  powA 4060 (compA 4060 (ruYpA p)
    (compA 4060 (compA 4060 ruLGensA[2]! (ruYpA p)) (ruInv ruLGensA[2]!))) 455

end CFSG.Sporadic.RuSchreier
