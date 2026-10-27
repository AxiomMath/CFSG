module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Monster.B.Pinned.Primes.Data

public section

namespace CFSG.Monster.B.Pinned

open CFSG.Blueprint

@[expose] def fiveCommInvRows : List (List ℕ) :=
  [[0, 3, 4, 0], [2, 0, 3, 3], [1, 2, 0, 3], [0, 2, 2, 0]]

end CFSG.Monster.B.Pinned
