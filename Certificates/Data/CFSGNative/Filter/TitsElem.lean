module

public import Certificates.Data.CFSGNative.SectionRank.TitsLocal

public section

namespace CFSG.SectionRank.Native.Tits

open CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[expose] def commOK (X Y : Table) : Bool := eqOn (compT nPts X Y) (compT nPts Y X)

@[expose] def elemProdT (X0 X1 X2 X3 X4 : Table) (n : Nat) : Table :=
  compT nPts (compT nPts (compT nPts (compT nPts (powT nPts (n % 2) X0)
    (powT nPts (n / 2 % 2) X1)) (powT nPts (n / 4 % 2) X2)) (powT nPts (n / 8 % 2) X3))
    (powT nPts (n / 16 % 2) X4)

@[expose] def elemOK (w0 w1 w2 w3 w4 : List Nat) : Bool :=
  let X0 := wT (texpand w0)
  let X1 := wT (texpand w1)
  let X2 := wT (texpand w2)
  let X3 := wT (texpand w3)
  let X4 := wT (texpand w4)
  allIn 0 tLetters.size (fun k => isManifest tLetters[k]!) &&
    (w0 ++ w1 ++ w2 ++ w3 ++ w4).all (· < tLetters.size) &&
    eqOn (powT nPts 2 X0) (idT nPts) && eqOn (powT nPts 2 X1) (idT nPts) &&
    eqOn (powT nPts 2 X2) (idT nPts) && eqOn (powT nPts 2 X3) (idT nPts) &&
    eqOn (powT nPts 2 X4) (idT nPts) &&
    commOK X0 X1 && commOK X0 X2 && commOK X0 X3 && commOK X0 X4 && commOK X1 X2 &&
    commOK X1 X3 && commOK X1 X4 && commOK X2 X3 && commOK X2 X4 && commOK X3 X4 &&
    allIn 0 31 (fun n => !eqOn (elemProdT X0 X1 X2 X3 X4 (n + 1)) (idT nPts))

end CFSG.SectionRank.Native.Tits
