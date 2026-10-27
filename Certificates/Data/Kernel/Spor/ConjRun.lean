module

public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KS.ConjRun

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum

@[expose] noncomputable def cgK (k : Nat) (S SI : Nat → Nat) (l : Nat) : Nat :=
  nIf(Nat.blt l k, S l, SI (Nat.sub l k))

@[expose] noncomputable def cgiK (k : Nat) (S SI : Nat → Nat) (l : Nat) : Nat :=
  nIf(Nat.blt l k, SI l, S (Nat.sub l k))

@[expose] noncomputable def cvK (n w m k R B : Nat) (S SI PL : Nat → Nat) (d : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat)
    (fun j p => nIf(Nat.beq j R, pg w m B p, n))
    (fun _ ih j p => nIf(Nat.beq j R, pg w m B p,
      strictN (r32 PL j) (fun e => strictN (Nat.land e (nat_lit 15)) (fun l =>
        nIf(Nat.blt l (Nat.add k k),
          strictN (pg w m (cgiK k S SI l) p) (fun q =>
            strictN (ih (Nat.shiftRight e (nat_lit 4)) q) (fun v =>
              nIf(Nat.blt v n, pg w m (cgK k S SI l) v, n))), n))))) d

@[expose] noncomputable def keyK (n w m k R B : Nat) (S SI PL : Nat → Nat) (d r j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => strictN acc (fun a => strictN (cvK n w m k R B S SI PL d j i) (fun v =>
      nIf(Nat.blt v n, Nat.add a (Nat.shiftLeft v (Nat.mul w i)),
        Nat.shiftLeft (nat_lit 1) (Nat.mul w r))))) r

@[expose] noncomputable def runGo (n w m k R B : Nat) (S SI PL : Nat → Nat) (d r lo : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun l ih s => strictN (keyK n w m k R B S SI PL d r (Nat.add lo l)) (fun key =>
      strictN (nIf(Nat.blt key s, key, nat_lit 0)) ih))

@[expose] noncomputable def runAt (n w m k R B : Nat) (S SI PL : Nat → Nat) (d r N lo len : Nat) :
    Bool :=
  Nat.blt (nat_lit 0) (runGo n w m k R B S SI PL d r lo len
    (nIf(Nat.blt (Nat.add lo len) N, keyK n w m k R B S SI PL d r (Nat.add lo len),
      Nat.shiftLeft (nat_lit 1) (Nat.mul w r))))

@[expose] noncomputable def runK (n w m k R B : Nat) (S SI PL : Nat → Nat) (d r N lo len : Nat) :
    Bool :=
  runAt n w m k R B S SI PL d r N lo (nIf(Nat.ble len (Nat.sub N lo), len, Nat.sub N lo))

end CFSG.KS.ConjRun

end
