module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KS.KeyWord

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def rf (w m R k : Nat) : Nat := fld(R, Nat.mul w k, m)

@[expose] noncomputable def wApp (w m : Nat) (L : Nat → Nat) (R o : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun j ih x => strictN (ih x) (fun v => pg w m (L (rf w m R (Nat.add o (Nat.succ j)))) v))

@[expose] noncomputable def wInv (w m : Nat) (LI : Nat → Nat) (R o : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun j ih x => strictN (pg w m (LI (rf w m R (Nat.add o (Nat.succ j)))) x) ih)

@[expose] noncomputable def lettersK (w m nL R o len : Nat) : Bool :=
  allN len (fun j => Nat.blt (rf w m R (Nat.add o (Nat.succ j))) nL)

@[expose] noncomputable def keyIsK (w m r KP R : Nat) (f : Nat → Nat) : Bool :=
  allN r (fun t => Nat.beq (rf w m R t) (f (pg w m KP t)))

@[expose] noncomputable def cjRowK (w m nL r : Nat) (L LI : Nat → Nat) (KP Y R : Nat) : Bool :=
  strictB (rf w m R r) (fun len => bAnd(lettersK w m nL R r len,
    keyIsK w m r KP R (fun p => wApp w m L R r len (pg w m Y (wInv w m LI R r len p)))))

@[expose] noncomputable def cjSlK (w m nL r KM : Nat) (L LI : Nat → Nat) (KP Y : Nat)
    (C : Nat → Nat) (N lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun i => bIf(Nat.blt i N,
    strictB (C i) (fun R => bAnd(cjRowK w m nL r L LI KP Y R,
      bIf(Nat.blt (Nat.succ i) N, Nat.blt (Nat.land R KM) (Nat.land (C (Nat.succ i)) KM), true))),
    true)))

@[expose] noncomputable def witK (w m r nS nL nY : Nat) (G L Y : Nat → Nat) (KP R o len c : Nat) :
    Bool :=
  strictB (Nat.add o (Nat.succ len)) (fun o' => strictB (rf w m R o') (fun len' =>
    bAnd(Nat.blt (nat_lit 0) c, bAnd(Nat.ble c nY, bAnd(lettersK w m nL R o' len',
      allN r (fun t => strictB (pg w m KP t) (fun p =>
        Nat.beq (wApp w m G R o len (wApp w m L R o' len' p))
          (wApp w m L R o' len' (pg w m (Y (Nat.sub c (nat_lit 1))) p)))))))))

@[expose] noncomputable def cubeK (w m r : Nat) (G : Nat → Nat) (KP R o len : Nat) : Bool :=
  bAnd(keyIsK w m r KP KP (fun p => wApp w m G R o len (wApp w m G R o len (wApp w m G R o len p))),
    bIf(keyIsK w m r KP R (fun p => p), false, true))

@[expose] noncomputable def syRowK (w m r nS nL nY KM : Nat) (G L Y : Nat → Nat) (KP : Nat)
    (E : Nat → Nat) (N i : Nat) : Bool :=
  strictB (E i) (fun R => strictB (Nat.add r (Nat.succ nS)) (fun o =>
  strictB (rf w m R o) (fun len =>
  bAnd(lettersK w m nS R o len,
  bAnd(keyIsK w m r KP R (fun p => wApp w m G R o len p),
  bAnd(allN nS (fun j => strictB (rf w m R (Nat.add r j)) (fun q => bAnd(Nat.blt q N,
    keyIsK w m r KP (E q) (fun p => pg w m (G j) (wApp w m G R o len p))))),
  bAnd(bIf(Nat.blt (Nat.succ i) N, Nat.blt (Nat.land R KM) (Nat.land (E (Nat.succ i)) KM), true),
  bIf(cubeK w m r G KP R o len,
    witK w m r nS nL nY G L Y KP R o len (rf w m R (Nat.add r nS)), true))))))))

@[expose] noncomputable def sySlK (w m r nS nL nY KM : Nat) (G L Y : Nat → Nat) (KP : Nat)
    (E : Nat → Nat) (N lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun i => bIf(Nat.blt i N,
    syRowK w m r nS nL nY KM G L Y KP E N i, true)))

end CFSG.KS.KeyWord

end
