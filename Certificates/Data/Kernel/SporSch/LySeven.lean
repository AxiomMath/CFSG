module

public import Certificates.Data.Kernel.SporSch.LySyl

public section

namespace CFSG.KS.SporSch.LySev

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def d3 (x t : Nat) : Nat := fld(x, Nat.mul (nat_lit 3) t, nat_lit 7)

@[expose] noncomputable def rowR (T : Nat → Nat) (rw i : Nat) : Nat :=
  fld(T (Nat.shiftRight i (nat_lit 6)), Nat.add (nat_lit 64) (Nat.mul rw (Nat.land i (nat_lit 63))),
    mask rw)

@[expose] noncomputable def linesRun (cs : List Char) : List Char → List (List Int) → Bool :=
  List.rec (motive := fun _ => List Char → List (List Int) → Bool)
    (fun acc LS => bAnd(List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) acc,
      List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) LS))
    (fun ch _ ih acc LS => bIf(Nat.beq (Char.toNat ch) (nat_lit 10),
      List.rec (motive := fun _ => Bool) false (fun L LS' _ =>
        bAnd(List.rec (motive := fun _ => Bool)
          (List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L)
          (fun _ _ _ => CFSG.KS.SporSch.LyM.parseK (List.reverse (List.cons ch acc)) L) acc,
          ih [] LS')) LS,
      ih (List.cons ch acc) LS))
    cs

@[expose] noncomputable def linesK (cs : List Char) (LS : List (List Int)) : Bool := linesRun cs [] LS

@[expose] noncomputable def digRun (cs : List Char) (DG : Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun i => i)
    (fun ch _ ih i => strictN (Char.toNat ch) (fun c =>
      nIf(Nat.beq c (nat_lit 10), ih i,
        nIf(bAnd(Nat.ble (nat_lit 48) c, bAnd(Nat.ble c (nat_lit 57),
            Nat.beq (Nat.sub c (nat_lit 48)) fld(DG, Nat.mul (nat_lit 4) i, nat_lit 15))),
          ih (Nat.succ i), nat_lit 1048576))))
    cs

@[expose] noncomputable def digK (cs : List Char) (DG n : Nat) : Bool :=
  Nat.beq (digRun cs DG (nat_lit 0)) n

@[expose] noncomputable def mv7K (R x : Nat) : Nat :=
  foldN (nat_lit 7) (fun r acc => Nat.lor acc (Nat.shiftLeft
    (Nat.mod (foldN (nat_lit 7) (fun c s => Nat.add s
      (Nat.mul (d3 R (Nat.add (Nat.mul (nat_lit 7) r) c)) (d3 x c))) (nat_lit 0)) (nat_lit 5))
    (Nat.mul (nat_lit 3) r))) (nat_lit 0)

@[expose] noncomputable def code7K (x : Nat) : Nat :=
  foldN (nat_lit 7) (fun r acc => Nat.add acc (Nat.mul (d3 x r) (Nat.pow (nat_lit 5) r)))
    (nat_lit 0)

@[expose] noncomputable def vFail : Nat := nat_lit 1048575

@[expose] noncomputable def vStep (GP E PL : Nat → Nat) (c h j st : Nat) : Nat :=
  strictN (Nat.land st (nat_lit 1048575)) (fun cnt => strictN (Nat.shiftRight st (nat_lit 20))
    (fun M => nIf(Nat.blt h cnt,
      strictN (mv7K (GP j) (E h)) (fun y => strictN (code7K y) (fun k =>
        nIf(hasBit M k, st,
          nIf(bAnd(Nat.blt cnt c, bAnd(Nat.beq (E cnt) y,
              Nat.beq (PL cnt) (Nat.add h (Nat.shiftLeft j (nat_lit 20))))),
            Nat.add (Nat.succ cnt) (Nat.shiftLeft (Nat.lor M (Nat.shiftLeft (nat_lit 1) k))
              (nat_lit 20)),
            vFail)))),
      st)))

@[expose] noncomputable def vRun (GP E PL : Nat → Nat) (kg c h₀ len st : Nat) : Nat :=
  foldUp len (fun i st => foldUp kg (fun j st => vStep GP E PL c (Nat.add h₀ i) j st) st) st

@[expose] noncomputable def red5 (QM Y : Nat) : Nat :=
  Nat.sub Y (Nat.mul (nat_lit 5)
    (Nat.land (Nat.shiftRight (Nat.mul Y (nat_lit 205)) (nat_lit 10)) QM))

@[expose] noncomputable def pack49 (Y b : Nat) : Nat :=
  foldN (nat_lit 49) (fun t acc => Nat.lor acc (Nat.shiftLeft
    fld(Y, Nat.add b (Nat.mul (nat_lit 20) t), nat_lit 7) (Nat.mul (nat_lit 3) t))) (nat_lit 0)

@[expose] noncomputable def imgs (KC : Nat → Nat) (QM x : Nat) : Nat :=
  red5 QM (foldN (nat_lit 49) (fun t acc => Nat.add acc (Nat.mul (d3 x t) (KC t))) (nat_lit 0))

@[expose] noncomputable def cFail : Nat := nat_lit 1048576

@[expose] noncomputable def cStep (ET WT PT : Nat → Nat) (c h Y j cnt : Nat) : Nat :=
  strictN (pack49 Y (Nat.mul (nat_lit 980) j)) (fun y =>
    strictN fld(rowR WT (nat_lit 95) h, Nat.mul (nat_lit 19) j, nat_lit 524287) (fun w =>
      nIf(Nat.blt w cnt, nIf(Nat.beq (rowR ET (nat_lit 147) w) y, cnt, cFail),
        nIf(bAnd(Nat.beq w cnt, bAnd(Nat.blt cnt c, bAnd(Nat.beq (rowR ET (nat_lit 147) cnt) y,
            Nat.beq (rowR PT (nat_lit 24) cnt) (Nat.add h (Nat.shiftLeft j (nat_lit 19)))))),
          Nat.succ cnt, cFail))))

@[expose] noncomputable def cRun (KC : Nat → Nat) (QM : Nat) (ET WT PT : Nat → Nat)
    (kg c h₀ len cnt : Nat) : Nat :=
  foldUp len (fun i cnt => strictN (Nat.add h₀ i) (fun h => nIf(Nat.blt h cnt,
    strictN (imgs KC QM (rowR ET (nat_lit 147) h)) (fun Y =>
      foldUp kg (fun j cnt => cStep ET WT PT c h Y j cnt) cnt),
    cnt))) cnt

end CFSG.KS.SporSch.LySev

end
