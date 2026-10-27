module

public import Certificates.Data.Kernel.Spor.Fi24Pair
public import Certificates.Data.Kernel.Spor.Fi24NetPt

public section

namespace CFSG.KC.Fi24PairP

open CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt
  CFSG.KC.Fi24Pair CFSG.KLC.Fi22

@[expose] noncomputable def gath (CF : Nat → Nat) (v : Nat) : Nat :=
  Nat.land (netF CF v) (ones (nat_lit 3240))

@[expose] noncomputable def fpl (FP : Nat → Nat) (k : Nat) : Nat :=
  sumBelow (nat_lit 3240) (nat_lit 51) (fun p =>
    Nat.shiftLeft (Nat.land (Nat.shiftRight (FP p) k) (nat_lit 1)) p)

@[expose] noncomputable def tf (P : Nat → Nat) (k : Nat) : Nat :=
  nIf(Nat.beq k (nat_lit 0), P (nat_lit 0), Nat.xor (P k) (P (nat_lit 0)))

@[expose] noncomputable def cfOK (CF : Nat → Nat) (FP : Nat → Nat) : Bool :=
  andB (masksOK CF) (Nat.rec (motive := fun _ => Bool) true
    (fun k ih => andB (Nat.beq (gath CF (tpl k)) (tf (fpl FP) k)) ih) (nat_lit 19))

@[expose] noncomputable def pl12 (PL j : Nat) : Nat :=
  Nat.land (Nat.shiftRight PL (Nat.mul (nat_lit 4096) j)) (ones (nat_lit 3240))

@[expose] noncomputable def sigP (NW : Nat → Nat → Nat) (CF : Nat → Nat) (NS l : Nat) : Bool :=
  andB (netValid (nat_lit 12) NS) (letB (planesNW NS) (fun PL =>
    andB (Nat.rec (motive := fun _ => Bool) true
        (fun j ih => andB (Nat.beq (gath CF (planeL NW l (netR CF (tpl j)))) (tf (pl12 PL) j)) ih)
        (nat_lit 12))
      (Nat.beq (gath CF (planeL NW l (netR CF (ones (nat_lit 3240))))) (ones (nat_lit 3240)))))

end CFSG.KC.Fi24PairP

end
