module

public import CFSG.Sporadic.J4.QTOutMatNative
public import CFSG.Sporadic.J4.QTOutCocNative
public import CFSG.Sporadic.J4.QTOutObsData
public import CFSG.Sporadic.J4.QTRankInvNative

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4.Native

@[expose] def aObs : Nat := cocW (dLet 0 1373 689) wObs

@[expose] def e5Rows : Array V2 := etaR cA

@[expose] def hRows : Array V2 := wordRowsOf wObs

@[expose] def gRows : Array V2 := mulRows (etaR (cB ^^^ aObs)) hRows

@[expose] def yRows : Array V2 := mulRows (mulRows rowsB rowsA) (baseInvs[1]?.getD idRows)

@[expose] def ximgs : Array V2 := xvs.map fun x => (frApply (frTable gRows) x).xor x

end CFSG.Sporadic.J4.QT
