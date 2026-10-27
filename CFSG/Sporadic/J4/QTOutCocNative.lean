module

public import CFSG.Sporadic.J4.QTOutCocData
public import CFSG.Sporadic.J4.QTMask

public section

namespace CFSG.Sporadic.J4.QT

@[expose] def dLet (e0 e1 e2 : Nat) (ℓ : Int) : Nat :=
  if ℓ = 1 then e0 else if ℓ = 2 then e1 else if ℓ = 3 then e2
  else if ℓ = -1 then act (-1) e0 else if ℓ = -2 then act (-2) e1
  else if ℓ = -3 then act (-3) e2 else 0

@[expose] def cocW (d : Int → Nat) (w : List Int) : Nat :=
  w.foldr (fun ℓ acc => d ℓ ^^^ act ℓ acc) 0

@[expose] def stage1 : List Nat :=
  (List.range 2048).filter fun e => rel01.all fun r => cocW (dLet 0 e 0) r == 0

@[expose] def stage2 : List Nat :=
  (List.range 2048).filter fun e => rel02.all fun r => cocW (dLet 0 0 e) r == 0

@[expose] def relAll (e1 e2 : Nat) : Bool :=
  rel01.all (fun r => cocW (dLet 0 e1 e2) r == 0) &&
    rel02.all (fun r => cocW (dLet 0 e1 e2) r == 0) &&
    relMix.all (fun r => cocW (dLet 0 e1 e2) r == 0)

end CFSG.Sporadic.J4.QT
