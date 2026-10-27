module

public import CFSG.Sporadic.SuzOddCore.Arrays
public import Certificates.Data.CFSGNative.Suz.Certificate
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Sporadic.SuzOddCore.Arrays
public meta import Certificates.Data.CFSGNative.Suz.Certificate
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native

@[expose] def relabelOK (alpha beta : Table) : Bool :=
  let r := relabelArr
  let a0 := certArr 0
  let a1 := certArr 1
  alpha.size == 22880 && beta.size == 22880 &&
    allLt 22880 fun i => r[ap alpha i]! == a0[r[i]!]! && r[ap beta i]! == a1[r[i]!]!

end CFSG.Sporadic.SuzOddCore
