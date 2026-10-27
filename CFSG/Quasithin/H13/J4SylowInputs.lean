module

public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Quasithin.H13.J4Words
public meta import CFSG.Sporadic.Schreier.J4SData

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native

@[expose] def fixedGenCols : List ℕ :=
  (List.range 2048).filter fun a => (List.range 4).all fun i => app11 generatorColumns[i]! a == a

end CFSG.Quasithin.H13.J4
