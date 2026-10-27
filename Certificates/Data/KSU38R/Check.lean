module

public import Certificates.Data.HuppertU38F.Data

public section

namespace KSU38R

open HuppertU38F CFSG.LieType.SeitzGeneration.HeisSmall

@[expose] def mpow (A : M3 Q8) : ℕ → M3 Q8
  | 0 => 1
  | n + 1 => A * mpow A n

@[expose] def isInvol (A : M3 Q8) : Bool := !isScalar A && isScalar (A * A)

@[expose] def commMod (A B : M3 Q8) : Bool := decide (∃ l : Q8, A * B = M3.smul l (B * A))

@[expose] def propto (A B : M3 Q8) : Bool := decide (∃ l : Q8, A = M3.smul l B)

@[expose] def mulVec (A : M3 Q8) (v : Col) : Col :=
  (A.a00 * v.1 + A.a01 * v.2.1 + A.a02 * v.2.2, A.a10 * v.1 + A.a11 * v.2.1 + A.a12 * v.2.2,
    A.a20 * v.1 + A.a21 * v.2.1 + A.a22 * v.2.2)

@[expose] def cycDet (A : M3 Q8) (v : Col) : Q8 :=
  (ofCols v (mulVec A v) (mulVec A (mulVec A v))).det

@[expose] def hasCyc (A : M3 Q8) : Bool := cols4.any fun v => decide (cycDet A v ≠ 0)

@[expose] def regFlag (A : M3 Q8) : Bool :=
  isScalar (A * A * A) && decide ((A * A * A).a00 ^ 3 = 1) && hasCyc A

@[expose] def e0 (_ : Unit := ()) : M3 Q8 := mat8 [1, 0, 0, 0, 8, 0, 0, 0, 9]

@[expose] def expCheck (_ : Unit := ()) : Bool := forallUnitary fun A => isScalar (mpow A 12)

@[expose] def invols (_ : Unit := ()) : List (M3 Q8) := guList.filter isInvol

@[expose] def noV4Check (_ : Unit := ()) : Bool :=
  let invs := invols ()
  forallUnitary (fun V => !isInvol V || decide (V ∈ invs)) &&
    invs.all fun U => invs.all fun V => !commMod U V || propto U V

@[expose] def repCheck (_ : Unit := ()) : Bool :=
  u38Table.all fun y => unitaryOk y.Y && entriesL4 y.Y && isScalar (y.Y * y.Y * y.Y)

@[expose] def e0Check (_ : Unit := ()) : Bool :=
  let E := e0 ()
  sgOk E && entriesL4 E && decide (E * E * E = 1) && !isScalar E &&
    u38Table.all (fun y => commMod E y.Y && !propto E y.Y && !propto E (y.Y * y.Y)) &&
    (u38Table.drop 3).all fun y => commutes E y.Y

@[expose] def regCheck (_ : Unit := ()) : Bool := (u38Table.take 3).all fun y => regFlag y.Y

@[expose] def dCheckOne (d : M3 Q8) : Bool :=
  forallUnitary fun Z =>
    !isScalar (Z * Z * Z) || isScalar Z || !commMod d Z || propto Z d || propto Z (d * d) ||
      (List.range 3).any fun j => regFlag (mpow d j * Z)

@[expose] def dCheck (_ : Unit := ()) : Bool := (u38Table.drop 3).all fun y => dCheckOne y.Y

@[expose] def u38RCheck (_ : Unit := ()) : Bool :=
  expCheck () && noV4Check () && repCheck () && e0Check () && regCheck () && dCheck ()

end KSU38R
