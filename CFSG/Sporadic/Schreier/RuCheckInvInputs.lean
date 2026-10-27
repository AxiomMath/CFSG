module

public import CFSG.Sporadic.Schreier.RuTreeEltA
public import CFSG.Sporadic.Schreier.RuWitArrays
public import CFSG.Sporadic.Schreier.RuCheckChains
public import CFSG.Sporadic.Schreier.RuEnum
public meta import CFSG.Sporadic.Schreier.RuTreeEltA
public meta import CFSG.Sporadic.Schreier.RuWitArrays
public meta import CFSG.Sporadic.Schreier.RuCheckChains
public meta import CFSG.Sporadic.Schreier.RuEnum
public meta import CFSG.Sporadic.Schreier.RuCheckTree
public import CFSG.Sporadic.Schreier.RuCheckTree
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def ruLevS : Array Level :=
  rawLevels 4060 (ruField4060 4) (ruBaseArr 4060 ruS4060ChainBase)

@[expose] def ruIsInvolA (t : Array ℕ) : Bool :=
  eqA 4060 (compA 4060 t t) (idA 4060) && !eqA 4060 t (idA 4060)

@[expose] def ruFixCount (t : Array ℕ) : ℕ := (fixedList 4060 t).length

@[expose] def ruAB2A : Array ℕ := compA 4060 ruA0A (powA 4060 ruA1A 2)

end CFSG.Sporadic.RuSchreier
