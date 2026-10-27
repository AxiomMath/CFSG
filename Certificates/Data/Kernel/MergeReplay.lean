module

public import Certificates.Data.Kernel.PackSet

public section

namespace CFSG.KC.MergeR

open CFSG.KC.Enum CFSG.KS CFSG.KC.Pack

@[expose] noncomputable def kOf (st : Nat) : Nat := fld(st, nat_lit 1, nat_lit 4294967295)

@[expose] noncomputable def szOff (w j : Nat) : Nat := Nat.add (nat_lit 33) (Nat.mul w j)

@[expose] noncomputable def parOff (w nw j : Nat) : Nat :=
  Nat.add (Nat.add (nat_lit 33) nw) (Nat.mul w j)

@[expose] noncomputable def ufK (w m nw st : Nat) (fuel x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun _ ih x => strictN fld(st, parOff w nw x, m) (fun p => nIf(Nat.beq p x, x, ih p))) fuel x

@[expose] noncomputable def recF (w m Lp j t : Nat) : Nat :=
  pg w m Lp (Nat.add (Nat.mul (nat_lit 3) j) t)

@[expose] noncomputable def unionK (n w m nw cnt Lp i u v ra rc st : Nat) : Nat :=
  strictN (kOf st) (fun k =>
  nIf(bAnd(Nat.blt ra n, bAnd(Nat.blt rc n, bAnd(Nat.blt k cnt,
      bAnd(Nat.beq (recF w m Lp k (nat_lit 0)) i, bAnd(Nat.beq (recF w m Lp k (nat_lit 1)) u,
        Nat.beq (recF w m Lp k (nat_lit 2)) v))))),
    strictN fld(st, szOff w ra, m) (fun sa => strictN fld(st, szOff w rc, m) (fun sc =>
    strictN (Nat.add sa sc) (fun s2 =>
    nIf(Nat.ble s2 m,
      strictN (setO st (nat_lit 1) (nat_lit 4294967295) (Nat.succ k)) (fun st1 =>
      nIf(Nat.blt sa sc,
        strictN (setO st1 (parOff w nw ra) m rc) (fun st2 => setO st2 (szOff w rc) m s2),
        strictN (setO st1 (parOff w nw rc) m ra) (fun st2 => setO st2 (szOff w ra) m s2))),
      nat_lit 1)))),
    nat_lit 1))

@[expose] noncomputable def genK (n w m nw cnt Lp : Nat) (Gp : Nat → Nat) (u v i st : Nat) :
    Nat :=
  nIf(Nat.beq (Nat.land st (nat_lit 1)) (nat_lit 1), st,
    strictN (Gp i) (fun g =>
    strictN (pg w m g u) (fun a => strictN (pg w m g v) (fun c =>
    strictN (ufK w m nw st n a) (fun ra => strictN (ufK w m nw st n c) (fun rc =>
    nIf(Nat.beq ra rc, st, unionK n w m nw cnt Lp i u v ra rc st)))))))

@[expose] noncomputable def procK (n w m nw nG cnt Lp : Nat) (Gp : Nat → Nat) (u v st : Nat) :
    Nat :=
  nIf(bAnd(Nat.blt u n, Nat.blt v n), foldUp nG (genK n w m nw cnt Lp Gp u v) st, nat_lit 1)

@[expose] noncomputable def stepK (n w m nw nG cnt Lp : Nat) (Gp : Nat → Nat) (b x h st : Nat) :
    Nat :=
  nIf(Nat.beq (Nat.land st (nat_lit 1)) (nat_lit 1), st,
    nIf(Nat.blt h (Nat.succ (kOf st)),
      nIf(Nat.beq h (nat_lit 0), procK n w m nw nG cnt Lp Gp b x st,
        strictN (Nat.sub h (nat_lit 1)) (fun j =>
        strictN (recF w m Lp j (nat_lit 0)) (fun i => strictN (recF w m Lp j (nat_lit 1)) (fun u =>
        strictN (recF w m Lp j (nat_lit 2)) (fun v =>
        nIf(bAnd(Nat.blt i nG, bAnd(Nat.blt u n, Nat.blt v n)),
          strictN (Gp i) (fun g => strictN (pg w m g u) (fun a => strictN (pg w m g v) (fun c =>
            procK n w m nw nG cnt Lp Gp a c st))),
          nat_lit 1)))))),
      st))

@[expose] noncomputable def initK (n w m nw b x : Nat) : Nat :=
  strictN (foldUp n (fun j s => strictN (setO s (szOff w j) m (nat_lit 1)) (fun s' =>
      setO s' (parOff w nw j) m j)) (nat_lit 0)) (fun s =>
    strictN (setO s (parOff w nw x) m b) (fun s' => setO s' (szOff w b) m (nat_lit 2)))

@[expose] noncomputable def searchK (n w m nw nG : Nat) (Gp : Nat → Nat) (b x cnt Lp : Nat) :
    Bool :=
  bAnd(Nat.beq m (mask w), bAnd(Nat.beq nw (Nat.mul n w), bAnd(Nat.ble n m,
    bAnd(Nat.ble (nat_lit 2) m, bAnd(Nat.blt b n, bAnd(Nat.blt x n,
    bAnd(Nat.blt cnt (nat_lit 4294967296),
    strictB (foldUp (Nat.succ n) (stepK n w m nw nG cnt Lp Gp b x) (initK n w m nw b x))
      (fun st => bAnd(Nat.beq (Nat.land st (nat_lit 1)) (nat_lit 0), Nat.beq (kOf st) cnt)))))))))

end CFSG.KC.MergeR

end
