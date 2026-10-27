module

public import Certificates.Data.Kernel.Misc.OmegaSixA

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.BfsK CFSG.KD.YamakiRepF CFSG.KC.Loop
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def fiveAt (S : Nat → Nat) (nS x : Nat) : Bool :=
  bIf(Nat.beq x ONE, true,
    strictY (MULF x x) fun s => bIf(Nat.beq (MULF (MULF s s) x) ONE, memK S 5 nS x, true))

@[expose] noncomputable def fiveChunk (R : Nat → Nat) (o n : Nat) (S : Nat → Nat) (nS L q : Nat) :
    Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t =>
    bIf(Nat.blt t n, strictY (recX R o t) (fiveAt S nS), true)

@[expose] noncomputable def wordK (x y : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) ONE (fun i _ acc => MULF (nIf(Nat.beq i 0, x, y)) acc) w

@[expose] noncomputable def relsK (ws : List (List Nat)) (x y : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ acc => bIf(Nat.beq (wordK x y w) ONE, acc, false)) ws

@[expose] noncomputable def inPW (P : Nat → Nat) (nP x : Nat) : Bool :=
  bIf(CFSG.KC.Misc.Clos.allR 0 nP fun m =>
    bIf(Nat.beq (fld(P m, 0, 68719476735)) x, false, true), false, true)

@[expose] noncomputable def pairAt (ws : List (List Nat)) (y : Nat) (P : Nat → Nat) (nP x : Nat) :
    Bool :=
  bIf(Nat.beq x ONE, true, bIf(relsK ws x y, inPW P nP x, true))

@[expose] noncomputable def pairChunk (R : Nat → Nat) (o n : Nat) (ws : List (List Nat)) (y : Nat)
    (P : Nat → Nat) (nP L q : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t =>
    bIf(Nat.blt t n, strictY (recX R o t) (pairAt ws y P nP), true)

@[expose] noncomputable def pwAt (G : Nat → Nat) (o n a y : Nat) (P : Nat → Nat) (m : Nat) : Bool :=
  strictY (P m) fun p => strictY (fld(p, 36, 65535)) fun j => strictY (recX G o j) fun t =>
    bAnd(Nat.blt j n, bAnd(Nat.beq (MULF t y) (MULF y t),
      Nat.beq (MULF t a) (MULF (fld(p, 0, 68719476735)) t)))

@[expose] noncomputable def pwOK (G : Nat → Nat) (o n a y : Nat) (P : Nat → Nat) (nP : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR 0 nP (pwAt G o n a y P)

end CFSG.KD.OmegaSix

end
