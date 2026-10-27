module

public import Certificates.Data.Kernel.SporSch.Co1Mat

public section

namespace CFSG.KS.SporSch.VOrb

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.M24

@[expose] noncomputable def recK (T : Nat → Nat) (k : Nat) : Nat :=
  fld(T (Nat.shiftRight k (nat_lit 5)), Nat.mul (nat_lit 64) (Nat.land k (nat_lit 31)),
    nat_lit 18446744073709551615)

@[expose] noncomputable def ptK (T : Nat → Nat) (k : Nat) : Nat :=
  Nat.land (recK T k) (nat_lit 16777215)

@[expose] noncomputable def iaK (T : Nat → Nat) (k : Nat) : Nat :=
  fld(recK T k, nat_lit 24, nat_lit 131071)

@[expose] noncomputable def ibK (T : Nat → Nat) (k : Nat) : Nat :=
  fld(recK T k, nat_lit 41, nat_lit 131071)

@[expose] noncomputable def msK (S : Nat → Nat) (k : Nat) : Nat :=
  Nat.land (recK S k) (nat_lit 131071)

@[expose] noncomputable def invK (S : Nat → Nat) (k : Nat) : Nat := fld(recK S k, nat_lit 17, nat_lit 131071)

@[expose] noncomputable def failC : Nat := nat_lit 1048576

@[expose] noncomputable def imgStep (T : Nat → Nat) (w i c : Nat) : Nat :=
  nIf(bAnd(Nat.ble i c, Nat.beq (ptK T i) w), nIf(Nat.beq i c, Nat.succ c, c), failC)

@[expose] noncomputable def bfsStep (A B : Nat) (T : Nat → Nat) (n h c : Nat) : Nat :=
  nIf(Nat.blt c failC, nIf(Nat.blt h n, nIf(Nat.blt h c,
    strictN (ptK T h) (fun v =>
      strictN (imgStep T (actK A v) (iaK T h) c) (fun c' =>
        nIf(Nat.blt c' failC, imgStep T (actK B v) (ibK T h) c', failC))),
    failC), c), failC)

@[expose] noncomputable def bfsSl (A B : Nat) (T : Nat → Nat) (n lo len c₀ c₁ : Nat) : Bool :=
  Nat.beq (foldUp len (fun d c => bfsStep A B T n (Nat.add lo d) c) c₀) c₁

@[expose] noncomputable def permSl (S T : Nat → Nat) (n lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun k => bIf(Nat.blt k n,
    strictB (msK S k) (fun m => strictB (invK S k) (fun r =>
      bAnd(Nat.blt m n, bAnd(Nat.blt r n, bAnd(Nat.beq (invK S m) k, bAnd(Nat.beq (msK S r) k,
        bIf(Nat.blt (Nat.succ k) n, Nat.blt (ptK T m) (ptK T (msK S (Nat.succ k))), true))))))),
    true)))

@[expose] noncomputable def bsK (T S : Nat → Nat) (v : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun lo _ => lo)
    (fun _ ih lo len => nIf(Nat.beq len (nat_lit 0), lo,
      strictN (Nat.shiftRight len (nat_lit 1)) (fun h =>
        nIf(Nat.blt (ptK T (msK S (Nat.add lo h))) v,
          ih (Nat.succ (Nat.add lo h)) (Nat.sub (Nat.sub len h) (nat_lit 1)), ih lo h))))

@[expose] noncomputable def memK (T S : Nat → Nat) (n v : Nat) : Bool :=
  strictB (bsK T S v (nat_lit 18) (nat_lit 0) n) (fun lo =>
    bIf(Nat.blt lo n, Nat.beq (ptK T (msK S lo)) v, false))

end CFSG.KS.SporSch.VOrb

end
