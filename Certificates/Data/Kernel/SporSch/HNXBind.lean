module

public import CFSG.Certificates.Kernel.Local.HN.X.Lib
public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.Sporadic.HNSchreier.PackedOrbitAccess
public import CFSG.Certificates.Kernel.Local.HN.Lib
public import CFSG.Certificates.Kernel.Local.LargeCore.Grp2

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KC.LL CFSG.Sporadic.HNSchreier.Native

@[expose] noncomputable def walkOK (f : Nat → Nat → Bool) (t : OrbitNats) (o : Nat) : Bool :=
  OrbitNats.rec (motive := fun _ => Nat → Bool)
    (fun w c bits o => allBlk (nat_lit 0) (fun j => f (Nat.add o j) (fldW bits (Nat.mul w j) w)) c)
    (fun ls _ _ iha ihb o => bAnd(iha o, strictB (Nat.add o ls) ihb)) t o

@[expose] def shapeOK (n : Nat) (t : OrbitNats) : Bool := t.valid && t.size == n

@[expose] noncomputable def vecAt (T : Nat → Nat) (i v : Nat) : Bool :=
  Nat.beq v (fldW (getRec T (nat_lit 464) i) (nat_lit 0) (nat_lit 399))

@[expose] noncomputable def imgAt (T : Nat → Nat) (s i v : Nat) : Bool :=
  Nat.beq v (fldW (getRec T (nat_lit 464) i) (Nat.add (nat_lit 399) (Nat.mul (nat_lit 21) s))
    (nat_lit 21))

@[expose] noncomputable def parAt (T : Nat → Nat) (i v : Nat) : Bool :=
  bIf(Nat.beq i (nat_lit 0), true, Nat.beq v
    (Nat.shiftRight (Nat.sub (fldW (getRec T (nat_lit 464) i) (nat_lit 441) (nat_lit 22)) (nat_lit 1))
      (nat_lit 1)))

@[expose] noncomputable def labAt (T : Nat → Nat) (i v : Nat) : Bool :=
  bIf(Nat.beq i (nat_lit 0), true, Nat.beq v
    (Nat.succ (Nat.land (Nat.sub (fldW (getRec T (nat_lit 464) i) (nat_lit 441) (nat_lit 22))
      (nat_lit 1)) (nat_lit 1))))

@[expose] def hnxShapeK (P : PackedOrbitData) : Bool :=
  P.dimension == 133 && shapeOK 1140000 P.vectors && shapeOK 1140000 P.alpha &&
    shapeOK 1140000 P.beta && shapeOK 1140000 P.parents && shapeOK 1140000 P.labels

@[expose] noncomputable def hnxBindK (T : Nat → Nat) (P : PackedOrbitData) : Bool :=
  bAnd(hnxShapeK P, bAnd(walkOK (vecAt T) P.vectors (nat_lit 0),
    bAnd(walkOK (imgAt T (nat_lit 0)) P.alpha (nat_lit 0),
    bAnd(walkOK (imgAt T (nat_lit 1)) P.beta (nat_lit 0),
    bAnd(walkOK (parAt T) P.parents (nat_lit 0), walkOK (labAt T) P.labels (nat_lit 0))))))

end CFSG.KS.SporSch

end
