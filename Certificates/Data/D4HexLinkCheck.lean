module

public import CFSG.LargeExtraspecial.S63CD4Inputs
public import Certificates.Data.D4HexBase

public section

namespace CFSG.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Monster.B.Co2.Native

@[expose] def linkCheckOn (cz : ClassData) : Bool :=
  gensOK d4Gens && classTreeOK d4Gens z0R cz.T cz.P cz.K cz.idx && cz.T.size == 819 &&
    permArrs.size == 8 &&
    allLt 8 fun j => allLt 819 fun i =>
      decide ((permArrs[j]!)[i]! < 819) &&
        cz.T[(permArrs[j]!)[i]!]! == conjR d4Gens[j]! cz.T[i]!

@[inline, expose] def lnPt (l k : Nat) : Nat := lineTab[3 * l + k]!

@[inline, expose] def lineKey (a b c : Nat) : Nat := (a * 819 + b) * 819 + c

@[expose] def sortKey (a b c : Nat) : Nat :=
  lineKey (min a (min b c)) (a + b + c - min a (min b c) - max a (max b c)) (max a (max b c))

@[expose] def lineIndex : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := {}
  for l in [0:2457] do
    m := m.insert (lineKey (lnPt l 0) (lnPt l 1) (lnPt l 2)) l
  return m

@[expose] def imgKey (j l : Nat) : Nat :=
  sortKey ((permArrs[j]!)[lnPt l 0]!) ((permArrs[j]!)[lnPt l 1]!) ((permArrs[j]!)[lnPt l 2]!)

@[expose] def lineCheck : Bool :=
  lnPt 0 0 == 0 && lnPt 0 1 == 1 && lnPt 0 2 == 5 &&
    (allLt 2457 fun l => decide (lnPt l 0 < lnPt l 1) && decide (lnPt l 1 < lnPt l 2) &&
      decide (lnPt l 2 < 819) && lineIndex.getD (lineKey (lnPt l 0) (lnPt l 1) (lnPt l 2)) 0 == l) &&
    allLt 8 fun j => allLt 2457 fun l =>
      decide (lineIndex.getD (imgKey j l) 0 < 2457) &&
        lineKey (lnPt (lineIndex.getD (imgKey j l) 0) 0) (lnPt (lineIndex.getD (imgKey j l) 0) 1)
          (lnPt (lineIndex.getD (imgKey j l) 0) 2) == imgKey j l

@[expose] def fixesLine0 (a : Array Nat) : Bool :=
  sortKey a[0]! a[1]! a[5]! == lineKey 0 1 5

@[expose] def baseFlagCheck : Bool :=
  (allLt 8 fun j => (permArrs[j]!)[0]! == 0 || fixesLine0 permArrs[j]!) &&
    [0, 1, 2, 6].all fun j => (permArrs[j]!)[0]! == 0 && fixesLine0 permArrs[j]!

@[expose] def linkCheck : Bool :=
  linkCheckOn (mkClass d4Gens z0R) && lineCheck && baseFlagCheck

end CFSG.D4Hex
