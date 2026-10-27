module

public import CFSG.Sporadic.SmallOddCore.LocalCheck

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

@[expose] def irrMemL (n : Nat) (L : List Table) (b : Table) : Bool := L.any fun y => tblEq n y b

@[expose] def irrWitOne (n : Nat) (px : List Table) (x : Table) : Bool :=
  px.any fun b₁ => !tblEq n b₁ x && px.any fun b₂ =>
    commTT n b₂ b₁ && !irrMemL n [x, b₁, compT n x b₁] b₂

@[expose] def irrWitTwo (n : Nat) (px : List Table) (x y : Table) : Bool :=
  px.any fun b => commTT n b y && !irrMemL n [x, y, compT n x y] b

@[expose] def irrSylowOK (n cap m : Nat) (sGens : List Table) (sift : Table → Bool)
    (extra : List Table) : Bool :=
  let E := (mulClosureH n sGens.toArray cap).1.toList
  let invs := E.filter (involOK n)
  let pool := (E ++ extra).filter fun b => permOK n b && involOK n b && sift b
  enumOK n cap m sGens && sGens.all (permOK n) &&
    invs.all fun x =>
      let px := pool.filter fun b => commTT n b x
      irrWitOne n px x && invs.all fun y => !commTT n x y || tblEq n x y || irrWitTwo n px x y

end CFSG.Sporadic.SmallOddCore
