module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

@[expose] noncomputable def firstIdx (c : Nat) (f : Nat → Bool) : Nat :=
  foldN c (fun i s => nIf(f i, i, s)) c

@[expose] noncomputable def failC : Nat := nat_lit 1099511627776

@[expose] noncomputable def stepC (n w m : Nat) (G E : Nat → Nat) (c PP LP h k cur : Nat) : Nat :=
  nIf(Nat.blt h cur,
    strictN (pcomp n w m (G k) (E h)) (fun t =>
    strictN (firstIdx c (fun j => Nat.beq (E j) t)) (fun j =>
      nIf(Nat.blt j cur, cur,
        nIf(bAnd(Nat.beq j cur, bAnd(Nat.beq fld(PP, Nat.mul (nat_lit 16) cur, nat_lit 65535) h,
            Nat.beq fld(LP, Nat.mul (nat_lit 8) cur, nat_lit 255) k)),
          Nat.succ cur, failC)))),
    failC)

@[expose] noncomputable def closureK (n w : Nat) (G : Nat → Nat) (kg : Nat) (E : Nat → Nat)
    (c PP LP bound : Nat) : Bool :=
  bAnd(szOK n w, bAnd(Nat.blt c bound, bAnd(Nat.blt (nat_lit 0) c, bAnd(Nat.blt kg (nat_lit 256),
  bAnd(Nat.blt c (nat_lit 65536),
  bAnd(Nat.beq (E (nat_lit 0)) (pidn n w),
  bAnd(Nat.beq (Nat.land PP (nat_lit 65535)) (nat_lit 0), bAnd(Nat.beq (Nat.land LP (nat_lit 255)) (nat_lit 0),
  bAnd(allN kg (fun k => canonK n w (mask w) (Nat.mul n w) (G k)),
  bAnd(allN c (fun i => canonK n w (mask w) (Nat.mul n w) (E i)),
  Nat.beq (foldUp c (fun h cur => foldUp kg (fun k cur =>
      stepC n w (mask w) G E c PP LP h k cur) cur) (nat_lit 1)) c))))))))))

end CFSG.KS.SporSch

end
