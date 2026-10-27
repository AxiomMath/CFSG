module

public import CFSG.Sporadic.J4.QTRankNative
public import CFSG.Sporadic.J4.QTRankInvData

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4.Native

@[expose] def tabE (e : Nat) : List Nat := seqT (pcSeq e)

@[expose] def isInvE (e : Nat) : Bool := compT (tabE e) (tabE e) == idT && tabE e != idT

@[expose] def kRows (i : Nat) : Array V2 := wordRows (locMats ()) (locInvs ()) (kWords.getD i [])

@[expose] def kRowsTab (_ : Unit) : Array (Array V2) := ((List.range 4).map kRows).toArray

@[expose] def KelRowsK (K : Array (Array V2)) (e : Nat) : Array V2 :=
  (pcSeq e).foldl (fun acc i => mulRows acc (K[i]?.getD idRows)) idRows

@[expose] def KelRows (e : Nat) : Array V2 := KelRowsK (kRowsTab ()) e

@[expose] def etaRT (T : Array (Array V2)) (c : Nat) : Array V2 := etaRows T 11 c

@[expose] def etaR (c : Nat) : Array V2 := etaRT (uTab (locMats ()) (locInvs ())) c

@[expose] def gMat (g : Nat) : Array V2 :=
  if g == 2 then baseInvs[1]?.getD idRows else baseMats[g]?.getD idRows

@[expose] def gInv (g : Nat) : Array V2 :=
  if g == 2 then baseMats[1]?.getD idRows else baseInvs[g]?.getD idRows

@[expose] def fuseOKT (T K : Array (Array V2)) (e : Nat) (y : Nat × Nat × Nat × Nat) : Bool :=
  let r := mulRows (etaRT T y.1) (KelRowsK K e)
  let ee := mulRows (mulRows (gMat y.2.1) (etaRT T y.2.2.1)) (gInv y.2.1)
  decide (y.2.1 < 3) && decide (0 < y.2.2.1) && decide (y.2.2.1 < 2048) && y.2.2.2 % 2 == 1 &&
    eqRows (powRows (mulRows r ee) y.2.2.2) idRows

@[expose] def imSet (t : List Nat) : List Nat :=
  ((List.range 2048).map fun m => m ^^^ actT t m).eraseDups

@[expose] def classCover (x : Nat × Nat × List (Nat × Nat × Nat × Nat)) : Bool :=
  let t := tabE x.1
  let im := imSet t
  (List.range 2048).all fun c =>
    c ^^^ actT t c != x.2.1 || x.2.2.any fun y => im.contains (c ^^^ y.1)

@[expose] def invOKT (T K : Array (Array V2)) (x : Nat × Nat × List (Nat × Nat × Nat × Nat)) :
    Bool :=
  decide (x.1 < 1024) && decide (x.2.1 < 2048) &&
    eqRows (mulRows (KelRowsK K x.1) (KelRowsK K x.1)) (etaRT T x.2.1) &&
    classCover x && x.2.2.all (fuseOKT T K x.1)

@[expose] def invAllOK : Bool :=
  let T := uTab (locMats ()) (locInvs ())
  let K := kRowsTab ()
  invData.all (invOKT T K)

end CFSG.Sporadic.J4.QT
