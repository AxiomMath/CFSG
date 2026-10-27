module

public import CFSG.Quasithin.H13.L32NKGCertInputs

public section

namespace CFSG.Quasithin.H13.KGCert

@[expose] def g22Invs : List (List ℕ) :=
  g22Elems.filter fun z => mulC z z == oneC && z != oneC

@[expose] def commC (x y : List ℕ) : Bool := mulC x y == mulC y x

@[expose] def g22RankCheck : Bool :=
  g22Invs.all fun a =>
    let Ca := g22Invs.filter fun b => commC a b
    Ca.all fun b =>
      b == a ||
        let ab := mulC a b
        let Cab := Ca.filter fun c => commC b c
        Cab.all fun c =>
          c == a || c == b || c == ab ||
            (Cab.filter fun e => commC c e).all fun e =>
              e == a || e == b || e == c || e == ab || e == mulC a c || e == mulC b c ||
                e == mulC ab c

end CFSG.Quasithin.H13.KGCert
