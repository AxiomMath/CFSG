module

public import CFSG.Sporadic.FischerOddCore.Fi22Cent
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22Cent
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22Ext
public import CFSG.Sporadic.FischerOddCore.Fi22Ext

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer

@[expose] def fi22CentWords (c : Nat) : Array (List Int) :=
  fi22WordsArr (fi22CentGenCount.getD c 0) (fi22CentStrongCount.getD c 0)
    (fi22CentDerivations.getD c [])

@[expose] def fi22CentOrderOK (c : Nat) : Bool :=
  let S := fi22CentStrong c
  let k := fi22CentGenCount.getD c 0
  let t := fi22ExtArr (21 + fi22CentCase c)
  rawChainOK 3510 (S.extract 0 (fi22CentK c)) S #[0, 1, 2, 3, 6, 4] (fi22CentWords c) 4 &&
    (rawOrbitSizes 3510 S #[0, 1, 2, 3, 6, 4]).prod == fi22CentOrders.getD c 0 &&
    allLt k fun j => fi22InP S[j]! && eqA 3510 (compA 3510 S[j]! t) (compA 3510 t S[j]!)

end CFSG.Sporadic.FischerOddCore
