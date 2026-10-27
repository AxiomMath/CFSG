module

public import Certificates.Data.Kernel.Fi22Twist.Lv

public section

namespace CFSG.KC.Fi22Twist

open CFSG.KC.Enum

@[expose] noncomputable def m72 : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 72)) (nat_lit 1)

@[expose] noncomputable def kAp (g c : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.lor (ap g (cg c (nat_lit 0))) (Nat.shiftLeft (ap g (cg c (nat_lit 1))) (nat_lit 12)))
      (Nat.lor (Nat.shiftLeft (ap g (cg c (nat_lit 2))) (nat_lit 24))
        (Nat.shiftLeft (ap g (cg c (nat_lit 3))) (nat_lit 36))))
    (Nat.lor (Nat.shiftLeft (ap g (cg c (nat_lit 4))) (nat_lit 48))
      (Nat.shiftLeft (ap g (cg c (nat_lit 5))) (nat_lit 60)))

@[expose] noncomputable def baseKey : Nat := nat_lit 4613375074479640576

@[expose] noncomputable def wfK (WF OF BF S : Nat → Nat) (u : Nat) : Bool :=
  strictB (WF u) fun r =>
  bIf(Nat.blt u (nat_lit 8),
    strictB (OF (nat_lit 4)) fun o4 =>
    bIf(Nat.beq u (nat_lit 0),
      strictB (OF (nat_lit 5)) fun o5 =>
      bAnd(Nat.beq (fld(r, nat_lit 24, nat_lit 4095)) (ap o5 (nat_lit 0)),
        Nat.beq (fld(r, nat_lit 36, nat_lit 4095)) (ap o5 (nat_lit 1))),
      strictB (fld(r, nat_lit 0, nat_lit 4095)) fun pa =>
      strictB (fld(r, nat_lit 12, nat_lit 4095)) fun g =>
      bAnd(Nat.blt pa u, bAnd(Nat.blt g (nat_lit 19),
        strictB (S g) fun s =>
        strictB (WF pa) fun q =>
        bAnd(fixB s (nat_lit 4), bAnd(Nat.beq (ap s (ap o4 pa)) (ap o4 u),
          bAnd(Nat.beq (fld(r, nat_lit 24, nat_lit 4095)) (ap s (fld(q, nat_lit 24, nat_lit 4095))),
            Nat.beq (fld(r, nat_lit 36, nat_lit 4095)) (ap s (fld(q, nat_lit 36, nat_lit 4095))))))))),
    strictB (Nat.sub u (nat_lit 8)) fun k =>
    strictB (BF k) fun b =>
    bIf(Nat.beq k (nat_lit 0),
      strictB (OF (nat_lit 4)) fun o4 =>
      allBlk (nat_lit 0) (fun p => strictB (WF p) fun q =>
        bAnd(Nat.beq (fld(b, Nat.mul (nat_lit 12) (Nat.succ p), nat_lit 4095)) (ap o4 p),
          bAnd(Nat.beq (fld(r, Nat.mul (nat_lit 24) p, nat_lit 4095)) (fld(q, nat_lit 24, nat_lit 4095)),
            Nat.beq (fld(r, Nat.add (Nat.mul (nat_lit 24) p) (nat_lit 12), nat_lit 4095))
              (fld(q, nat_lit 36, nat_lit 4095))))) (nat_lit 8),
      strictB (fld(b, nat_lit 108, nat_lit 4095)) fun pa =>
      bAnd(Nat.blt pa k, bAnd(Nat.blt (Nat.shiftRight b (nat_lit 120)) (nat_lit 19),
        strictB (S (Nat.shiftRight b (nat_lit 120))) fun s =>
        strictB (WF (Nat.add (nat_lit 8) pa)) fun q =>
        allBlk (nat_lit 0) (fun f => Nat.beq (fld(r, Nat.mul (nat_lit 12) f, nat_lit 4095))
          (ap s (fld(q, Nat.mul (nat_lit 12) f, nat_lit 4095)))) (nat_lit 16)))))

@[expose] noncomputable def leafV (M Dj CK : Nat → Nat) (h offC szC full v ef : Nat) : Bool :=
  bIf(Nat.ble (nat_lit 32768) ef,
    strictB (Nat.sub ef (nat_lit 32768)) fun i =>
    bAnd(Nat.blt i szC, Nat.beq (fld(CK (Nat.add offC i), nat_lit 0, m72)) full),
    bIf(Nat.beq ef (nat_lit 1), Bool.not (relK Dj h full),
      bAnd(Nat.ble (nat_lit 2) ef,
        strictB (Nat.sub ef (nat_lit 2)) fun w =>
        bAnd(Nat.blt w (nat_lit 135),
          strictB (Nat.div w (nat_lit 27)) fun mm =>
          strictB (Nat.mod w (nat_lit 27)) fun e =>
          Bool.not (Nat.beq (eb M (ap (Dj e) (cg full mm)) v) (eb M (ap (Dj e) (bp mm)) (bp (nat_lit 5))))))))

@[expose] noncomputable def leafK (T D M BF WF X E K CK : Nat → Nat) (j n offC szC : Nat) : Bool :=
  strictB (K n) fun row =>
  strictB (T (fld(row, nat_lit 0, nat_lit 65535))) fun t0 =>
  strictB (T (fld(row, nat_lit 16, nat_lit 65535))) fun t1 =>
  strictB (T (fld(row, nat_lit 32, nat_lit 65535))) fun t2 =>
  strictB (E n) fun ev =>
  strictB (X j) fun h =>
  strictB (Nat.shiftRight row (nat_lit 48)) fun code =>
  (fun (Dj : Nat → Nat) (a : Nat → Nat) =>
    strictB (Nat.lor (Nat.lor (a (bp (nat_lit 0))) (Nat.shiftLeft (a (bp (nat_lit 1))) (nat_lit 12)))
      (Nat.shiftLeft (a (bp (nat_lit 2))) (nat_lit 24))) fun cs =>
    bAnd(Nat.beq (Nat.shiftRight code (nat_lit 126)) (nat_lit 0),
      allBlk (nat_lit 0) (fun s => strictB (fld(code, Nat.mul (nat_lit 14) s, nat_lit 16383)) fun f =>
        bIf(Nat.beq f (nat_lit 0), true,
          strictB (Nat.div (Nat.sub f (nat_lit 1)) (nat_lit 8)) fun k =>
          strictB (Nat.mod (Nat.sub f (nat_lit 1)) (nat_lit 8)) fun p =>
          bAnd(Nat.blt k (nat_lit 720),
            strictB (BF k) fun b =>
            strictB (WF (Nat.add (nat_lit 8) k)) fun w =>
            strictB (Nat.lor cs (Nat.lor (Nat.shiftLeft (a (fld(b, nat_lit 0, nat_lit 4095))) (nat_lit 36))
              (Nat.shiftLeft (a (fld(b, Nat.mul (nat_lit 12) (Nat.succ p), nat_lit 4095))) (nat_lit 48)))) fun c4s =>
            allBlk (nat_lit 0) (fun q =>
              strictB (a (fld(w, Nat.mul (nat_lit 12) (Nat.add (Nat.mul (nat_lit 2) p) q), nat_lit 4095))) fun v =>
              leafV M Dj CK h offC szC (Nat.lor c4s (Nat.shiftLeft v (nat_lit 60))) v
                (fld(ev, Nat.mul (nat_lit 16) (Nat.add (Nat.mul (nat_lit 2) s) q), nat_lit 65535)))
              (nat_lit 2)))) (nat_lit 9)))
  (fun e => D (Nat.add (Nat.mul (nat_lit 27) j) e)) (fun x => ap t0 (ap t1 (ap t2 x)))

@[expose] noncomputable def orbK (CK G : Nat → Nat) (gof ng off sz i : Nat) : Bool :=
  strictB (CK (Nat.add off i)) fun r =>
  strictB (fld(r, nat_lit 0, m72)) fun key =>
  strictB (fld(r, nat_lit 72, nat_lit 255)) fun d =>
  bAnd(bIf(Nat.beq i (nat_lit 0), true,
      Nat.blt (fld(CK (Nat.sub (Nat.add off i) (nat_lit 1)), nat_lit 0, m72)) key),
    bAnd(bIf(Nat.beq d (nat_lit 0), Nat.beq key baseKey,
        strictB (fld(r, nat_lit 80, nat_lit 4095)) fun pa =>
        strictB (fld(r, nat_lit 92, nat_lit 15)) fun g =>
        bAnd(Nat.blt pa sz, bAnd(Nat.blt g ng,
          strictB (CK (Nat.add off pa)) fun q =>
          bAnd(Nat.beq (Nat.succ (fld(q, nat_lit 72, nat_lit 255))) d,
            Nat.beq key (kAp (G (Nat.add gof g)) (fld(q, nat_lit 0, m72))))))),
      allBlk (nat_lit 0) (fun m => strictB (fld(r, Nat.add (nat_lit 96) (Nat.mul (nat_lit 12) m), nat_lit 4095)) fun x =>
        bAnd(Nat.blt x sz,
          Nat.beq (fld(CK (Nat.add off x), nat_lit 0, m72)) (kAp (G (Nat.add gof m)) key))) ng))

@[expose] noncomputable def subK (UK CK : Nat → Nat) (offU offC szC i : Nat) : Bool :=
  strictB (UK (Nat.add offU i)) fun r =>
  strictB (fld(r, nat_lit 176, nat_lit 4095)) fun x =>
  bAnd(Nat.blt x szC, Nat.beq (fld(CK (Nat.add offC x), nat_lit 0, m72)) (fld(r, nat_lit 0, m72)))

@[expose] noncomputable def commK (G D : Nat → Nat) (gof j m : Nat) : Bool :=
  strictB (G (Nat.add gof m)) fun g =>
  allBlk (nat_lit 0) (fun t =>
    strictB (D (Nat.add (Nat.mul (nat_lit 27) j)
      (nIf(Nat.beq t (nat_lit 0), nat_lit 9, nIf(Nat.beq t (nat_lit 1), nat_lit 3, nat_lit 1))))) fun x =>
    Nat.beq (kAp g (kAp x baseKey)) (kAp x (kAp g baseKey))) (nat_lit 3)

@[expose] noncomputable def normK (NF CG UG UK : Nat → Nat) (j m gofC gofU ngU offU szU : Nat) : Bool :=
  strictB (NF (Nat.add (Nat.mul (nat_lit 8) j) m)) fun r =>
  strictB (CG (Nat.add gofC m)) fun c =>
  strictB (fld(r, nat_lit 0, m72)) fun ci =>
  bAnd(Nat.beq (kAp c ci) baseKey,
    allBlk (nat_lit 0) (fun t =>
      strictB (fld(r, Nat.add (nat_lit 72) (Nat.mul (nat_lit 12) t), nat_lit 4095)) fun x =>
      bAnd(Nat.blt x szU,
        Nat.beq (fld(UK (Nat.add offU x), nat_lit 0, m72)) (kAp c (kAp (UG (Nat.add gofU t)) ci)))) ngU)

@[expose] noncomputable def relV (Dj : Nat → Nat) (h lv : Nat) : Bool :=
  allBlk (nat_lit 0) (fun t =>
    strictB (fld(h, Nat.add (nat_lit 8) (Nat.mul (nat_lit 16) t), nat_lit 65535)) fun u =>
    strictB (Nat.land u (nat_lit 15)) fun l =>
    strictB (fld(u, nat_lit 4, nat_lit 15)) fun l' =>
    strictB (Nat.shiftRight u (nat_lit 8)) fun e =>
    bAnd(Nat.blt e (nat_lit 27), bAnd(Nat.ble l lv, bAnd(Nat.ble l' lv,
      Nat.beq (ap (Dj e) (bp l)) (bp l')))))
    (Nat.land h (nat_lit 255))

@[expose] noncomputable def rowR (R r : Nat) : Nat :=
  fld(R, Nat.mul (nat_lit 42120) r, Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 42120)) (nat_lit 1))

@[expose] noncomputable def dfK (DF : Nat → Nat) (R j e : Nat) : Bool :=
  strictB (DF (Nat.add (Nat.mul (nat_lit 27) j) e)) fun d =>
  bIf(Nat.beq e (nat_lit 0), allN (nat_lit 3510) (fun i => Nat.beq (ap d i) i),
    strictB (nIf(Nat.beq (Nat.mod e (nat_lit 3)) (nat_lit 0),
      nIf(Nat.beq (Nat.mod e (nat_lit 9)) (nat_lit 0), nat_lit 0, nat_lit 1), nat_lit 2)) fun t =>
    strictB (rowR R (Nat.add (Nat.mul (nat_lit 3) j) t)) fun g =>
    strictB (DF (Nat.sub (Nat.add (Nat.mul (nat_lit 27) j) e)
      (nIf(Nat.beq t (nat_lit 2), nat_lit 1, nIf(Nat.beq t (nat_lit 1), nat_lit 3, nat_lit 9))))) fun d' =>
    allN (nat_lit 3510) (fun i => Nat.beq (ap d i) (ap d' (ap g i))))

end CFSG.KC.Fi22Twist

end
