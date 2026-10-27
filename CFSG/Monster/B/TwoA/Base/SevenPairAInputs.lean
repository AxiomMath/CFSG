module

public import CFSG.Monster.B.TwoA.Base.M22
public import CFSG.Monster.B.TwoA.Base.TwoPair
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import Mathlib.GroupTheory.GroupAction.ConjAct
public meta import CFSG.Monster.B.TwoA.Census.PermCert
public meta import CFSG.Monster.B.TwoA.Census.PermBFS
public meta import CFSG.Monster.Code.Weights

public section

namespace CFSG.Monster.B.TwoA

open CFSG.Monster.Code CFSG.Monster.B.TwoA.Census CFSG.Sporadic.Mathieu

open scoped Pointwise

@[expose] def gensP : Array (Array ℕ) :=
  #[#[0, 1, 10, 13, 11, 12, 6, 7, 16, 23, 2, 4, 5, 3, 17, 22, 8, 14, 18, 19, 20, 21, 15, 9],
    #[0, 1, 15, 6, 18, 13, 16, 5, 21, 17, 3, 11, 12, 23, 20, 4, 10, 19, 2, 22, 14, 8, 9, 7],
    #[1, 0, 12, 13, 17, 18, 21, 23, 19, 16, 20, 22, 2, 3, 15, 14, 9, 4, 5, 8, 10, 6, 11, 7]]

@[expose] def sig2Arr : Array ℕ :=
  #[0, 1, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

@[expose] def sig3Arr : Array ℕ :=
  #[0, 1, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 16, 17, 18, 19, 20, 21, 22, 23]

@[expose] def orbA2Cert : TreeCert := bfsCert aconj gensP sig2Arr 2000

@[expose] def orbA3Cert : TreeCert := bfsCert aconj gensP sig3Arr 1000

end CFSG.Monster.B.TwoA
