module

public import CFSG.Monster.Existence.ELevelCheck

@[expose] public section

namespace CFSG.Monster.Tri.Leech

open CFSG.Monster CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel CFSG.Monster.VisCert
  CFSG.Monster.Existence CFSG.Monster.B.TwoA.Census

def fixCountX (i : ℕ) : ℕ :=
  let tt := tT i
  let td := tD i
  (shortPacked.filter fun x => kapX tt td x == x).length

end CFSG.Monster.Tri.Leech
