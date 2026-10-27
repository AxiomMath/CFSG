module

public import CFSG.Sporadic.J4.QTRankWitNative

public section

namespace CFSG.Quasithin.B45Exc

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

@[expose] def C11 (_ : Unit) : Array V2 :=
  let T := uTab (locMats ()) (locInvs ())
  let t := etaRT T 1
  let g := mulRows (mulRows (gMat 0) (gMat 1)) (gMat 0)
  let gi := mulRows (mulRows (gInv 0) (gInv 1)) (gInv 0)
  mulRows t (mulRows (mulRows gi t) g)

end CFSG.Quasithin.B45Exc
