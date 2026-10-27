module

public import Certificates.Data.Kernel.Misc.F7Mat

public section

namespace CFSG.KC.Misc.F7

@[expose] noncomputable def m8W : Nat :=
  sumN (nat_lit 360) fun k => Nat.shiftLeft (nat_lit 255) (Nat.mul (nat_lit 32) k)

@[expose] noncomputable def red7W (v : Nat) : Nat :=
  Nat.sub v (Nat.mul (nat_lit 7)
    (Nat.land (Nat.shiftRight (Nat.mul v (nat_lit 4682)) (nat_lit 15)) m8W))

@[expose] noncomputable def wMaskC (r : Nat) : Nat :=
  sumN (nat_lit 28) fun m => ifN (Nat.blt (Nat.add r (Nat.mul (nat_lit 13) m)) (nat_lit 360))
    (Nat.shiftLeft (nat_lit 7) (Nat.mul (nat_lit 3) (Nat.add r (Nat.mul (nat_lit 13) m))))
    (nat_lit 0)

@[expose] noncomputable def wSpread (r : Nat) : Nat :=
  sumN (nat_lit 28) fun m => Nat.shiftLeft (nat_lit 1)
    (Nat.add (Nat.mul (nat_lit 29) r) (Nat.mul (nat_lit 377) m))

@[expose] noncomputable def wMaskT (r : Nat) : Nat :=
  sumN (nat_lit 28) fun m => ifN (Nat.blt (Nat.add r (Nat.mul (nat_lit 13) m)) (nat_lit 360))
    (Nat.shiftLeft (nat_lit 7) (Nat.mul (nat_lit 32) (Nat.add r (Nat.mul (nat_lit 13) m))))
    (nat_lit 0)

@[expose] noncomputable def widenF (c : Nat) : Nat :=
  red7W (sumN (nat_lit 13) fun r =>
    Nat.land (Nat.mul (Nat.land c (wMaskC r)) (wSpread r)) (wMaskT r))

@[expose] noncomputable def revM (B : Nat) : Nat :=
  sumN (nat_lit 45) fun k =>
    Nat.shiftLeft (row B k) (Nat.mul (nat_lit 1440) (Nat.sub (nat_lit 44) k))

@[expose] noncomputable def f7SP : Nat :=
  sumN (nat_lit 45) fun t => Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 1437) t)

@[expose] noncomputable def f7SpMask : Nat :=
  sumN (nat_lit 45) fun k => Nat.shiftLeft (nat_lit 7) (Nat.mul (nat_lit 1440) k)

@[expose] noncomputable def rowImgK (r Bv : Nat) : Nat :=
  red7 (fld(Nat.mul (Nat.land (Nat.mul r f7SP) f7SpMask) Bv, nat_lit 63360, rowMask))

@[expose] noncomputable def f7Img (S Bv : Nat) : Nat :=
  sumN (nat_lit 8) fun c => Nat.shiftLeft
    (rowImgK (fld(S, Nat.mul (nat_lit 135) c, nat_lit 43556142965880123323311949751266331066367))
      Bv) (Nat.mul (nat_lit 1440) c)

@[expose] noncomputable def f7ColMask : Nat :=
  sumN (nat_lit 8) fun i => Nat.shiftLeft (nat_lit 4294967295) (Nat.mul (nat_lit 1440) i)

@[expose] noncomputable def f7Seven : Nat :=
  sumN (nat_lit 8) fun i => Nat.shiftLeft (nat_lit 7) (Nat.mul (nat_lit 1440) i)

@[expose] noncomputable def f7Col (U p : Nat) : Nat :=
  Nat.sub f7Seven (Nat.land (Nat.shiftRight U (Nat.mul (nat_lit 32) p)) f7ColMask)

@[expose] noncomputable def pvF (pw c : Nat) : Nat := fld(pw, Nat.mul (nat_lit 6) c, nat_lit 63)

@[expose] noncomputable def inSpan8 (U V pw : Nat) : Bool :=
  Nat.beq (red7W (Nat.add U (sumN (nat_lit 8) fun c =>
    Nat.mul (f7Col U (pvF pw c)) (row V c)))) (nat_lit 0)

@[expose] noncomputable def m001 : Nat :=
  sumN (nat_lit 360) fun k => Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 3) k)

@[expose] noncomputable def colMask3 : Nat :=
  sumN (nat_lit 8) fun i => Nat.shiftLeft (nat_lit 7) (Nat.mul (nat_lit 135) i)

@[expose] noncomputable def f7Canon (c pw : Nat) : Bool :=
  andB (allN (nat_lit 8) fun k => andB (Nat.beq (fld(c, Nat.mul (nat_lit 135) k,
      Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 3) (pvF pw k))) (nat_lit 1))) (nat_lit 0))
      (Nat.beq (fld(c, Nat.mul (nat_lit 3) (pvF pw k), colMask3))
        (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 135) k))))
    (andB (allN (nat_lit 7) fun k => Nat.blt (pvF pw k) (pvF pw (Nat.succ k)))
      (andB (Nat.blt (pvF pw (nat_lit 7)) (nat_lit 45))
        (andB (Nat.beq (Nat.land (Nat.land c (Nat.land (Nat.shiftRight c (nat_lit 1))
            (Nat.shiftRight c (nat_lit 2)))) m001) (nat_lit 0))
          (Nat.blt c (Nat.shiftLeft (nat_lit 1) (nat_lit 1080))))))

end CFSG.KC.Misc.F7

end
