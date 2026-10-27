module

public import Certificates.Data.Kernel.Misc.F2BfsRec
public import Certificates.Data.Kernel.Misc.G24

public section

namespace CFSG.KC.F2BfsRec

open CFSG.KLie.CT CFSG.KC.M1F2

@[expose] noncomputable def edgesK2 (d w lb ng : Nat) (CF G : Nat → Nat) (N r X : Nat) : Bool :=
  allN ng fun j => strictB (fldOf d w r j) fun t =>
    andB (Nat.blt t N) (Nat.beq (elemAt d w lb ng CF t) (CFSG.KC.Misc.G24.mulF2 d X (G j)))

@[expose] noncomputable def recK2 (d w lb ng : Nat) (CF G : Nat → Nat) (N k : Nat) : Bool :=
  strictB (recAt d w lb ng CF k) fun r => strictB (elemOf d r) fun X =>
    andB (edgesK2 d w lb ng CF G N r X) (
    andB (Nat.blt k (fldOf d w r ng)) (
    andB (Nat.beq (rowK d w r (fldOf d w r ng) ng) (nextM d w lb ng CF N k))
      (sortK d w lb ng CF N k (fldOf d w r (Nat.succ ng)))))

@[expose] noncomputable def genR (d w lb ng : Nat) (CF : Nat → Nat) (j : Nat) : Nat :=
  elemAt d w lb ng CF (fldOf d w (recAt d w lb ng CF (nat_lit 0)) j)

@[expose] noncomputable def memK (d w lb ng : Nat) (CF : Nat → Nat) (N t X : Nat) : Bool :=
  andB (Nat.blt t N) (Nat.beq (elemAt d w lb ng CF t) X)

@[expose] noncomputable def sortedAt (d w lb ng : Nat) (CF : Nat → Nat) (p : Nat) : Nat :=
  elemAt d w lb ng CF (fldOf d w (recAt d w lb ng CF p) (Nat.succ ng))

@[expose] noncomputable def gapK (d w lb ng : Nat) (CF : Nat → Nat) (N p X : Nat) : Bool :=
  bIf(Nat.beq p N, Nat.blt X (sortedAt d w lb ng CF (nat_lit 0)),
    andB (Nat.blt p N) (andB (Nat.blt (sortedAt d w lb ng CF p) X)
      (bIf(Nat.blt (Nat.succ p) N, Nat.blt X (sortedAt d w lb ng CF (Nat.succ p)), true))))

end CFSG.KC.F2BfsRec

end
