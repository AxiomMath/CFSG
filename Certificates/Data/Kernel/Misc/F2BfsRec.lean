module

public import Certificates.Data.Kernel.M1F2

public section

namespace CFSG.KC.F2BfsRec

open CFSG.KLie.CT CFSG.KC.M1F2

@[expose] noncomputable def recW (d w ng : Nat) : Nat := Nat.add (Nat.mul d d) (Nat.mul (Nat.add ng 2) w)

@[expose] noncomputable def recAt (d w lb ng : Nat) (CF : Nat → Nat) (k : Nat) : Nat :=
  fget (CF (Nat.shiftRight k lb)) (Nat.land k (maskN lb)) (recW d w ng)

@[expose] noncomputable def elemOf (d r : Nat) : Nat := Nat.land r (maskN (Nat.mul d d))

@[expose] noncomputable def fldOf (d w r i : Nat) : Nat :=
  Nat.land (Nat.shiftRight r (Nat.add (Nat.mul d d) (Nat.mul w i))) (maskN w)

@[expose] noncomputable def elemAt (d w lb ng : Nat) (CF : Nat → Nat) (k : Nat) : Nat :=
  elemOf d (recAt d w lb ng CF k)

@[expose] noncomputable def stK (w t m : Nat) : Nat :=
  nIf(Nat.blt t m, m, nIf(Nat.beq t m, Nat.succ m, pw2 w))

@[expose] noncomputable def rowK (d w r m ng : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) m (fun j acc => stK w (fldOf d w r j) acc) ng

@[expose] noncomputable def nextM (d w lb ng : Nat) (CF : Nat → Nat) (N k : Nat) : Nat :=
  nIf(Nat.blt (Nat.succ k) N, fldOf d w (recAt d w lb ng CF (Nat.succ k)) ng, N)

@[expose] noncomputable def edgesK (d w lb ng : Nat) (CF G : Nat → Nat) (N r X : Nat) : Bool :=
  allN ng fun j => strictB (fldOf d w r j) fun t =>
    andB (Nat.blt t N) (Nat.beq (elemAt d w lb ng CF t) (mulF d X (G j)))

@[expose] noncomputable def sortK (d w lb ng : Nat) (CF : Nat → Nat) (N k s : Nat) : Bool :=
  andB (Nat.blt s N) (bIf(Nat.blt (Nat.succ k) N,
    Nat.blt (elemAt d w lb ng CF s)
      (elemAt d w lb ng CF (fldOf d w (recAt d w lb ng CF (Nat.succ k)) (Nat.succ ng))), true))

@[expose] noncomputable def recK (d w lb ng : Nat) (CF G : Nat → Nat) (N k : Nat) : Bool :=
  strictB (recAt d w lb ng CF k) fun r => strictB (elemOf d r) fun X =>
    andB (edgesK d w lb ng CF G N r X) (
    andB (Nat.blt k (fldOf d w r ng)) (
    andB (Nat.beq (rowK d w r (fldOf d w r ng) ng) (nextM d w lb ng CF N k))
      (sortK d w lb ng CF N k (fldOf d w r (Nat.succ ng)))))

@[expose] noncomputable def headK (d w lb ng : Nat) (CF : Nat → Nat) : Bool :=
  strictB (recAt d w lb ng CF (nat_lit 0)) fun r =>
    andB (Nat.beq (elemOf d r) (idF d)) (Nat.beq (fldOf d w r ng) (nat_lit 1))

end CFSG.KC.F2BfsRec

end
