module

public import CFSG.Sporadic.Schreier.TitsLocalCheck
public import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Sporadic.Schreier.TitsChain
public import CFSG.Sporadic.Schreier.TitsChain

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def titsSLevels : Array Level := rawLevels 1755 titsSArrs (baseArr 1755 titsSBase)

@[expose] def titsHLevels : Array Level := rawLevels 1755 titsHArrs (baseArr 1755 titsHBase)

@[expose] def titsNLevels : Array Level := rawLevels 1755 titsNArrs (baseArr 1755 titsNBase)

@[expose] def titsJLevels : Array Level := rawLevels 1755 titsJArrs (baseArr 1755 titsJBase)

@[expose] def titsKLevels : Array Level := rawLevels 1755 titsKArrs (baseArr 1755 titsKBase)

@[expose] def titsZArr : Array ℕ := wordArr 1755 titsDerivedArrs titsCenterWord

@[expose] def titsCHJ : List (Array ℕ) :=
  survivors5 1755 titsHLevels fun a => commutesAll 1755 a (titsJArrs.extract 0 4)

@[expose] def titsCNK : List (Array ℕ) :=
  survivors5 1755 titsNLevels fun a => commutesAll 1755 a (titsKArrs.extract 0 2)

@[expose] def anyEq (L : List (Array ℕ)) (a : Array ℕ) : Bool := L.any fun c => eqA 1755 a c

end CFSG.Sporadic.Schreier.Tits
