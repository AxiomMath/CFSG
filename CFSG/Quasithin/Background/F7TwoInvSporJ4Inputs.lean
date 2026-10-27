module

public import CFSG.Sporadic.J4.QTRankInvNative

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

@[expose] def j4CommEtaA (_ : Unit) : Array V2 :=
  let r := etaR 1
  mulRows (mulRows (mulRows r rowsA) r) rowsA

@[expose] def j4CommEtaB (_ : Unit) : Array V2 :=
  let r := etaR 1
  mulRows (mulRows (mulRows r rowsB) r) (gMat 2)

@[expose] def j4CommAB (_ : Unit) : Array V2 :=
  mulRows (mulRows (mulRows rowsA rowsB) rowsA) (gMat 2)

end CFSG.Quasithin.F7Two
