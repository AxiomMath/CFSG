module

public import Certificates.Data.Kernel.DELK

public section

namespace Certificates.DELK

open Certificates.DepASmall Certificates.TwoDepSmall Certificates.TwoDepSmallLow

@[expose] def kPairsOK (Ps : List (List GGDepANPair)) : Bool :=
  Ps.all fun l => l.all fun q =>
    decide (q.1.length = 6) && decide (q.2.length = 6) && ggDepANDot 3 q.2 q.1 == 2

@[expose] def kMat6 (m : List (List Nat)) : Bool :=
  decide (m.length = 6) && m.all fun c => decide (c.length = 6)

@[expose] def kConjShapes (C : List KConj) : Bool :=
  C.all fun c => kMat6 c.2.2.1 && kMat6 c.2.2.2

end Certificates.DELK

end
