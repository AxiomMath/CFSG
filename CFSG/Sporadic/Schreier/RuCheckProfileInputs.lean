
module

public import CFSG.Sporadic.Schreier.RuCheckSylowBase
public meta import CFSG.Sporadic.Schreier.RuCheckSylowBase

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def ruIsZF (x : Array ℕ) : Bool := eqA 1920 x (idA 1920) || eqA 1920 x ruZF

@[expose] def ruOrd8F (x : Array ℕ) : Bool :=
  let x2 := compA 1920 x x
  let x4 := compA 1920 x2 x2
  ruIsZF (compA 1920 x4 x4) && !(ruIsZF x4)

@[expose] def ruTv (v : ℕ) : Array ℕ :=
  compA 1920 (compA 1920 (powA 1920 (ruSF 0) (v % 2)) (powA 1920 (ruSF 2) (v / 2 % 2)))
    (powA 1920 (ruSF 3) (v / 4 % 2))

end CFSG.Sporadic.RuSchreier
