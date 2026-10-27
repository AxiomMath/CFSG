module

public import Certificates.Data.Kernel.Fi22Twist.Search

public section

namespace CFSG.KC.Fi22Twist

open CFSG.KC.Enum

@[expose] noncomputable def szL (i : Nat) : Nat :=
  fld(Nat.lor (Nat.lor (Nat.lor (nat_lit 3510) (Nat.shiftLeft (nat_lit 2816) (nat_lit 12)))
    (Nat.lor (Nat.shiftLeft (nat_lit 567) (nat_lit 24)) (Nat.shiftLeft (nat_lit 720) (nat_lit 36))))
    (Nat.lor (Nat.shiftLeft (nat_lit 8) (nat_lit 48)) (Nat.shiftLeft (nat_lit 2) (nat_lit 60))),
    Nat.mul (nat_lit 12) i, nat_lit 4095)

@[expose] noncomputable def offK (j : Nat) : Nat :=
  fld(Nat.lor (Nat.lor (Nat.lor (nat_lit 0) (Nat.shiftLeft (nat_lit 81) (nat_lit 12)))
    (Nat.lor (Nat.shiftLeft (nat_lit 405) (nat_lit 24)) (Nat.shiftLeft (nat_lit 891) (nat_lit 36))))
    (Nat.lor (Nat.shiftLeft (nat_lit 2835) (nat_lit 48)) (Nat.shiftLeft (nat_lit 2997) (nat_lit 60))),
    Nat.mul (nat_lit 12) j, nat_lit 4095)

@[expose] noncomputable def fixB (x i : Nat) : Bool :=
  allBlk (nat_lit 0) (fun m => Nat.beq (ap x (bp m)) (bp m)) i

@[expose] noncomputable def lvK (OF PF S : Nat → Nat) (u : Nat) : Bool :=
  strictB (Nat.div u (nat_lit 20)) fun i =>
  strictB (Nat.mod u (nat_lit 20)) fun g =>
  strictB (OF i) fun o =>
  strictB (PF i) fun ps =>
  strictB (szL i) fun n =>
  bIf(Nat.beq g (nat_lit 19),
    bAnd(Nat.beq (ap o (nat_lit 0)) (bp i),
      allN n (fun k => strictB (ap o k) fun x =>
        bAnd(Nat.blt x (nat_lit 3510), Nat.beq (ap ps x) k))),
    strictB (S g) fun s =>
    bIf(fixB s i,
      allN n (fun k => strictB (ap s (ap o k)) fun y => strictB (ap ps y) fun q =>
        bAnd(Nat.blt q n, Nat.beq (ap o q) y)),
      true))

@[expose] noncomputable def tfPtK (T TT OF : Nat → Nat) (f : Nat) : Bool :=
  strictB (TT f) fun r =>
  strictB (T f) fun t =>
  strictB (fld(r, nat_lit 0, nat_lit 255)) fun i =>
  strictB (fld(r, nat_lit 8, nat_lit 65535)) fun k =>
  bAnd(Nat.blt i (nat_lit 3), bAnd(Nat.blt k (szL i),
    bAnd(Nat.beq (ap t (bp i)) (ap (OF i) k), fixB t i)))

@[expose] noncomputable def passL (Dj : Nat → Nat) (a : Nat → Nat) (o m h cs d k : Nat) : Bool :=
  strictB (a (ap o k)) fun v =>
  bAnd(Nat.beq (fld(m, v, nat_lit 1)) (nat_lit 1),
    relK Dj h (Nat.lor cs (Nat.shiftLeft v (Nat.mul (nat_lit 12) d))))

@[expose] noncomputable def scanL (Dj : Nat → Nat) (a : Nat → Nat) (o m h cs d r : Nat) : Nat :=
  foldN (szL d) (fun k s =>
    nIf(Nat.blt s (nat_lit 4096),
      nIf(passL Dj a o m h cs d k,
        nIf(bAnd(Nat.blt (nat_lit 0) s,
            Nat.beq (fld(r, Nat.add (nat_lit 84) (Nat.mul (nat_lit 12) s), nat_lit 4095)) (Nat.succ k)),
          Nat.sub s (nat_lit 1), nat_lit 4096),
        s),
      s))
    (fld(r, nat_lit 80, nat_lit 255))

@[expose] noncomputable def childL (TT LF KF : Nat → Nat) (r d j t : Nat) : Bool :=
  strictB (fld(r, Nat.add (nat_lit 96) (Nat.mul (nat_lit 12) t), nat_lit 4095)) fun kc =>
  strictB (Nat.add (fld(r, nat_lit 64, nat_lit 65535)) t) fun ci =>
  strictB (nIf(Nat.blt d (nat_lit 2), LF ci, KF ci)) fun c =>
  strictB (fld(c, Nat.mul (nat_lit 16) d, nat_lit 65535)) fun fi =>
  strictB (TT fi) fun q =>
  bAnd(allBlk (nat_lit 0) (fun mm => Nat.beq (fld(c, Nat.mul (nat_lit 16) mm, nat_lit 65535))
      (fld(r, Nat.mul (nat_lit 16) mm, nat_lit 65535))) d,
    bAnd(Nat.beq (fld(q, nat_lit 0, nat_lit 255)) d,
      bAnd(Nat.beq (Nat.succ (fld(q, nat_lit 8, nat_lit 65535))) kc,
        bAnd(Nat.blt fi (nat_lit 891),
          bIf(Nat.blt d (nat_lit 2),
            bAnd(Nat.beq (fld(c, nat_lit 48, nat_lit 255)) (Nat.succ d),
              Nat.beq (fld(c, nat_lit 56, nat_lit 255)) j),
            bAnd(Nat.ble (offK j) ci, Nat.blt ci (offK (Nat.succ j))))))))

@[expose] noncomputable def nodeK (T TT OF M D GF LF KF : Nat → Nat) (n : Nat) : Bool :=
  strictB (LF n) fun r =>
  strictB (fld(r, nat_lit 48, nat_lit 255)) fun d =>
  strictB (fld(r, nat_lit 56, nat_lit 255)) fun j =>
  strictB (T (fld(r, nat_lit 0, nat_lit 65535))) fun t0 =>
  strictB (T (fld(r, nat_lit 16, nat_lit 65535))) fun t1 =>
  bAnd(Nat.blt d (nat_lit 3), bAnd(Nat.blt j (nat_lit 5),
    (fun (Dj : Nat → Nat) (a : Nat → Nat) =>
      strictB (Nat.land (Nat.lor (a (bp (nat_lit 0))) (Nat.shiftLeft (a (bp (nat_lit 1))) (nat_lit 12)))
        (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 12) d)) (nat_lit 1))) fun cs =>
      strictB (maskL M Dj cs d d) fun m =>
      strictB (fld(GF j, Nat.mul (nat_lit 1024) d, Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1024)) (nat_lit 1)))
        fun h =>
      strictB (OF d) fun o =>
      bAnd(Nat.beq (scanL Dj a o m h cs d r) (nat_lit 0),
        allBlk (nat_lit 0) (fun t => childL TT LF KF r d j t) (fld(r, nat_lit 80, nat_lit 255))))
    (fun e => D (Nat.add (Nat.mul (nat_lit 27) j) e))
    (fun x => nIf(Nat.beq d (nat_lit 0), x,
      ap t0 (nIf(Nat.beq d (nat_lit 1), x, ap t1 x))))))

@[expose] noncomputable def rootK (LF : Nat → Nat) (n : Nat) : Bool :=
  strictB (LF n) fun r =>
  bAnd(Nat.beq (fld(r, nat_lit 48, nat_lit 255)) (nat_lit 0),
    Nat.beq (fld(r, nat_lit 56, nat_lit 255)) n)

end CFSG.KC.Fi22Twist

end
