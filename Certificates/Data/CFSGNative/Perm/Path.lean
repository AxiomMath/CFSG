module

public import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace CFSG.Perm.Native

open CFSG.Sporadic.Th.Native

@[inline, expose] def orbPathAt (n : Nat) (T : Tree) (letters : Array Table) (lv : Array Nat)
    (k : Nat) : Bool :=
  let p := ap T.pts k
  p < n && ap T.pos p == k &&
    (k == 0 || (ap T.par k < k && lv.contains (ap T.lab k) &&
      ap letters[ap T.lab k]! (ap T.pts (ap T.par k)) == p))

@[expose] def orbPathOK (n root : Nat) (T : Tree) (letters : Array Table) (lv : Array Nat) : Bool :=
  0 < T.pts.size && ap T.pts 0 == root && allIn 0 T.pts.size (orbPathAt n T letters lv)

end CFSG.Perm.Native

end
