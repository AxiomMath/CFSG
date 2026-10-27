module

public import Certificates.Data.Kernel.Misc.G24
public import CFSG.LargeExtraspecial.AS35QCoNative
public import Std.Data.HashSet

public section

namespace CFSG.KC.C21205

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.G24

@[expose] noncomputable def fld (Q w i : Nat) : Nat :=
  Nat.land (Nat.shiftRight Q (Nat.mul w i)) (Nat.sub (Nat.shiftLeft 1 w) 1)

@[expose] noncomputable def mulK (c d : Nat) : Nat := mulF2 6 c d

@[expose] noncomputable def transK (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p acc => Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight c
      (Nat.add (Nat.mul 6 (Nat.mod p 6)) (Nat.div p 6))) 1) p)) 36

@[expose] noncomputable def isSpK (c : Nat) : Bool :=
  Nat.beq (mulK (mulK (transK c) CFSG.LargeExtraspecial.AS35QCo.Native.jc) c)
    CFSG.LargeExtraspecial.AS35QCo.Native.jc

@[expose] noncomputable def pairK (c ci : Nat) : Bool :=
  andB (isSpK c) (andB (Nat.beq (mulK c ci) CFSG.LargeExtraspecial.AS35QCo.Native.idc)
    (Nat.beq (mulK ci c) CFSG.LargeExtraspecial.AS35QCo.Native.idc))

@[expose] noncomputable def conjK (x e : Nat) : Bool :=
  letB (fld e 2 0) fun k => letB (fld (Nat.shiftRight e 2) 36 0) fun m =>
    letB (Nat.shiftRight e 38) fun mi =>
      andB (pairK m mi)
        (Nat.beq (mulK x m) (mulK m (CFSG.LargeExtraspecial.AS35QCo.Native.repc k)))

@[expose] noncomputable def sylowK (PQ i0 ng G R PD CJ : Nat) : Bool :=
  andB (Nat.blt i0 512) <|
  andB (Nat.beq (fld PQ 36 i0) CFSG.LargeExtraspecial.AS35QCo.Native.idc) <|
  andB (allN 511 fun i => Nat.blt (fld PQ 36 i) (fld PQ 36 (Nat.succ i))) <|
  andB (allN 4 fun k => letB (CFSG.LargeExtraspecial.AS35QCo.Native.repc k) fun r =>
    andB (isSpK r) (Nat.beq (mulK r r) CFSG.LargeExtraspecial.AS35QCo.Native.idc)) <|
  andB (allN ng fun j => letB (fld G 72 j) fun e =>
    pairK (fld e 36 0) (Nat.shiftRight e 36)) <|
  andB (allN 512 fun i => letB (fld PQ 36 i) fun x => allN ng fun j =>
    Nat.beq (fld PQ 36 (fld R 9 (Nat.add (Nat.mul ng i) j))) (mulK x (fld (fld G 72 j) 36 0))) <|
  andB (allN 512 fun i => orB (Nat.beq i i0) (letB (fld PD 24 i) fun e =>
    letB (fld e 9 0) fun p => letB (fld (Nat.shiftRight e 9) 4 0) fun j => andB (Nat.blt j ng) (andB
        (Nat.beq (Nat.shiftRight e 13) (Nat.succ (Nat.shiftRight (fld PD 24 p) 13)))
        (Nat.beq (fld PQ 36 i) (mulK (fld PQ 36 p) (fld (fld G 72 j) 36 0)))))) <|
  allN 512 fun i => letB (fld PQ 36 i) fun x =>
    impB (andB (Nat.beq (mulK x x) CFSG.LargeExtraspecial.AS35QCo.Native.idc)
      (notB (Nat.beq x CFSG.LargeExtraspecial.AS35QCo.Native.idc))) (conjK x (fld CJ 74 i))

end CFSG.KC.C21205

end
