module

public import CFSG.Sporadic.Schreier.RuOrbLDefs
public meta import CFSG.Sporadic.Schreier.RuOrbLDefs
public import CFSG.Sporadic.Schreier.RuCheckInv
public meta import CFSG.Sporadic.Schreier.RuCheckInv
public import CFSG.Sporadic.Schreier.RuCheckL
public meta import CFSG.Sporadic.Schreier.RuCheckL

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def ruLevL : Array Level := rawLevels 4060 (ruField4060 5) (ruBaseArr 4060 ruLChainBase)

@[expose] def ruLevC : Array Level := rawLevels 4060 (ruField4060 1) (ruBaseArr 4060 ruCBase)

@[expose] def ruCommTest (l t : Array ℕ) : Bool := allLt 4060 fun x => l[t[x]!]! == t[l[x]!]!

@[expose] def ruSqZA (r : Array ℕ) : Bool := allLt 4060 fun x => r[r[x]!]! == ruZA[x]!

@[expose] def ruCentCountOf (t : Array ℕ) : ℕ := count2 4060 ruLevL fun l => ruCommTest l t

@[expose] def ruCentCount (k : ℕ) : ℕ := ruCentCountOf (ruRepZA k)

@[expose] def ruCentCounts : List ℕ :=
  [2, 2, 4, 4, 4, 2, 4, 4, 4, 4, 4, 4, 2, 2, 32, 256, 32, 4, 32]

@[expose] def ruOrd14 (x : Array ℕ) : Bool :=
  eqA 4060 (powA 4060 x 14) (idA 4060) && !eqA 4060 (powA 4060 x 7) (idA 4060) &&
    !eqA 4060 (powA 4060 x 2) (idA 4060)

@[expose] def ruFibTest (g gi r : Array ℕ) : Bool :=
  let x := compA 4060 (compA 4060 g r) gi
  let ax := compA 4060 ruA0A x
  eqA 4060 (powA 4060 ax 13) (idA 4060) &&
    eqA 4060 (powA 4060 (compA 4060 (compA 4060 ax ruA0A) (compA 4060 x x)) 29) (idA 4060)

@[expose] def ruFibCountOf (g gi : Array ℕ) : ℕ :=
  count3 4060 ruLevC fun r => ruSqZA r && ruFibTest g gi r

@[expose] def ruFibCount (k : ℕ) : ℕ :=
  ruFibCountOf (ruTEltA 64 (ruReps.getD k 0)) (ruTEltInvA 64 (ruReps.getD k 0))

end CFSG.Sporadic.RuSchreier
