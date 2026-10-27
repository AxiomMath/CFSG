module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open

@[expose] def Chev2DirectTag (t : StatedLieTag) : Prop :=
  t = .twistedB2 ∨ t = .twistedF4 ∨ t = .Tits ∨ t = .G2

end CFSG.LocalAnalysis.WeakClosure81
