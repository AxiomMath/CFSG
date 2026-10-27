module

public import Certificates.Data.A6CMat6

public section

namespace Certificates.A6C

@[expose] def refl0M6 (_ : Unit := ()) : Mat :=
  #[2,0,0,0,0,0, 0,1,0,0,0,0, 0,0,1,0,0,0, 0,0,0,1,0,0, 0,0,0,0,1,0, 0,0,0,0,0,1]

@[expose] def inRefl (rF : Rec) (c : Mat) : Bool := rF.L.toList.any fun y => eqP y c

@[expose] def partK1 (rF : Rec) : Bool := classOK 6 (gens6 ()) (refl0M6 ()) rF 252

@[expose] def partK2 (rA rCT rF : Rec) : Bool :=
  let g0 := g0M6 ()
  let K0 := k0Of 6 g0 rCT
  let I := idN 6
  rA.L.toList.all fun a =>
    !(relP 6 a g0) ||
      (let K := K0.filter fun c => commP 6 c a
       K.all fun y1 => K.all fun y2 =>
         eqP y1 I || eqP y2 I || eqP y1 y2 || inRefl rF y1 || inRefl rF y2 ||
           inRefl rF (mulN 6 y1 y2))

end Certificates.A6C
