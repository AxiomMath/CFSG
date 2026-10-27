module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Monster.B.Pinned.Primes.Data
public import Certificates.Data.CFSGNative.MonsterB.Primes
public import Certificates.Data.Kernel.BabyMonster.Bridge24

public section

namespace CFSG.Sporadic.Bridge.B

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Monster.B.Bin
  CFSG.Monster.B.Primes.Native TauCeti
open scoped Matrix

abbrev pres : GroupPresentation := TauCeti.Sporadic.BabyMonster.presentation

end CFSG.Sporadic.Bridge.B
