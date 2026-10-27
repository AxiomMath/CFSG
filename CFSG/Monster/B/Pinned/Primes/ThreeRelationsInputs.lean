module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Monster.B.Pinned.Primes.Data
public import Certificates.Data.CFSGNative.MonsterB.Primes
public import Certificates.Data.Kernel.BabyMonster.Pair24

public section

namespace CFSG.Monster.B.Pinned

open Bin Primes.Native CFSG.Blueprint

@[expose] def threeCommInvRows : List (List ℕ) :=
  [[0, 2, 0, 2, 1, 2, 0, 0], [1, 0, 1, 2, 1, 2, 0, 2], [0, 2, 0, 0, 1, 2, 2, 0],
    [1, 1, 0, 0, 2, 0, 2, 1], [2, 2, 2, 1, 0, 1, 1, 0], [1, 1, 1, 0, 2, 0, 1, 1],
    [0, 0, 1, 1, 2, 2, 0, 2], [0, 1, 0, 2, 0, 2, 1, 0]]

end CFSG.Monster.B.Pinned
