module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Orders.Mat3
public import Certificates.Data.Kernel.Spor.Fi24FixK

public section

namespace CFSG.KC.Fi24Ext

open CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24FixK

@[expose] noncomputable def digV (CT : Nat → Nat) (c0 w : Nat) (id : Bool) (i j : Nat) : Nat :=
  nIf(Nat.blt j c0, nIf(andB id (Nat.beq i j), nat_lit 1, nat_lit 0),
    nIf(Nat.blt j (Nat.add c0 w),
      strictN (Nat.add (Nat.mul w i) (Nat.sub j c0)) (fun t =>
        trit (CT (Nat.div t (nat_lit 4))) (Nat.mod t (nat_lit 4))),
      nat_lit 0))

@[expose] noncomputable def digRowsOK (P1 P2 : Nat) (CT : Nat → Nat) (c0 w : Nat) (id : Bool)
    (lo m hi : Nat) : Bool :=
  allBelow m hi (fun t => letB (Nat.add lo t) (fun i =>
    letB (Nat.mul (nat_lit 781) i) (fun o =>
    letB (Nat.land (Nat.shiftRight P1 o) RM) (fun r1 =>
    letB (Nat.land (Nat.shiftRight P2 o) RM) (fun r2 =>
      allBelow (nat_lit 781) (nat_lit 13) (fun j => entOK r1 r2 j (digV CT c0 w id i j)))))))

@[expose] noncomputable def zeroFromOK (P1 P2 r : Nat) : Bool :=
  andB (Nat.beq (Nat.shiftRight P1 (Nat.mul (nat_lit 781) r)) (nat_lit 0))
    (Nat.beq (Nat.shiftRight P2 (Nat.mul (nat_lit 781) r)) (nat_lit 0))

@[expose] noncomputable def RS : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 253)) (nat_lit 1)

@[expose] noncomputable def padOK (X Z : Nat) : Bool :=
  andB (allBelow (nat_lit 253) (nat_lit 4) (fun i =>
      andB (Nat.beq (Nat.land (Nat.shiftRight X (Nat.mul (nat_lit 253) i)) RS)
          (Nat.land (Nat.shiftRight Z (Nat.mul (nat_lit 781) i)) RM))
        (Nat.beq (Nat.land (Nat.shiftRight X (Nat.add (nat_lit 64009) (Nat.mul (nat_lit 253) i))) RS)
          (Nat.land (Nat.shiftRight Z (Nat.add (nat_lit 609961) (Nat.mul (nat_lit 781) i))) RM))))
    (andB (Nat.beq (Nat.shiftRight (Nat.land Z (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 609961))
        (nat_lit 1))) (nat_lit 197593)) (nat_lit 0))
      (andB (Nat.beq (Nat.shiftRight Z (nat_lit 807554)) (nat_lit 0))
        (Nat.beq (Nat.shiftRight X (nat_lit 128018)) (nat_lit 0))))

@[expose] noncomputable def chunkIn (FS : Nat → Bool) (ST : Nat → Nat) (ONE g : Nat) : Nat :=
  nIf(FS g, ONE, ST (Nat.sub g (nat_lit 1)))

@[expose] noncomputable def addM3 (N LO X Y : Nat) : Nat :=
  CFSG.KC.Ord.add3 N (Nat.land X LO) (Nat.shiftRight X N) (Nat.land Y LO) (Nat.shiftRight Y N)

end CFSG.KC.Fi24Ext

end
