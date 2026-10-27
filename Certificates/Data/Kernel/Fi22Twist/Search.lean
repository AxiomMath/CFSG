module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Fi22Twist

open CFSG.KC.Enum

@[expose] noncomputable def ap (p x : Nat) : Nat := fld(p, Nat.mul (nat_lit 12) x, nat_lit 4095)

@[expose] noncomputable def bp (i : Nat) : Nat :=
  fld(nat_lit 4613375074479640576, Nat.mul (nat_lit 12) i, nat_lit 4095)

@[expose] noncomputable def eb (M : Nat → Nat) (x y : Nat) : Nat := fld(M x, y, nat_lit 1)

@[expose] noncomputable def cg (cs i : Nat) : Nat := fld(cs, Nat.mul (nat_lit 12) i, nat_lit 4095)

@[expose] noncomputable def fullM : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 3510)) (nat_lit 1)

@[expose] noncomputable def maskL (M Dj : Nat → Nat) (cs nm i : Nat) : Nat :=
  foldN (Nat.mul (nat_lit 27) nm) (fun r s =>
    (fun mm e => nIf(Nat.beq (eb M (ap (Dj e) (bp mm)) (bp i)) (nat_lit 1),
        Nat.land s (M (ap (Dj e) (cg cs mm))),
        Nat.land s (Nat.xor fullM (M (ap (Dj e) (cg cs mm))))))
      (Nat.div r (nat_lit 27)) (Nat.mod r (nat_lit 27))) fullM

@[expose] noncomputable def relK (Dj : Nat → Nat) (H cs : Nat) : Bool :=
  allBlk (nat_lit 0) (fun t =>
    (fun u => Nat.beq (cg cs (fld(u, nat_lit 4, nat_lit 15)))
      (ap (Dj (Nat.shiftRight u (nat_lit 8))) (cg cs (Nat.land u (nat_lit 15)))))
      (fld(H, Nat.add (nat_lit 8) (Nat.mul (nat_lit 16) t), nat_lit 65535)))
    (Nat.land H (nat_lit 255))

@[expose] noncomputable def g4K (M Dj : Nat → Nat) (c3 v : Nat) : Bool :=
  allBlk (nat_lit 0) (fun e => Nat.beq (eb M (ap (Dj e) c3) v) (eb M (ap (Dj e) (nat_lit 3)) (nat_lit 6)))
    (nat_lit 27)

@[expose] noncomputable def stepK (M Dj : Nat → Nat) (H3 H4 m3 m4 cs : Nat) (a : Nat → Nat)
    (k ob s : Nat) : Nat :=
  strictN (a (fld(ob, nat_lit 0, nat_lit 4095))) fun c3 =>
    nIf(bAnd(Nat.beq (fld(m3, c3, nat_lit 1)) (nat_lit 1),
        relK Dj H3 (Nat.lor cs (Nat.shiftLeft c3 (nat_lit 36)))),
      foldBlk (nat_lit 0) (fun p s2 =>
        strictN (a (fld(ob, Nat.mul (nat_lit 12) (Nat.succ p), nat_lit 4095))) fun v =>
          nIf(bAnd(Nat.beq (fld(m4, v, nat_lit 1)) (nat_lit 1),
              bAnd(relK Dj H4 (Nat.lor (Nat.lor cs (Nat.shiftLeft c3 (nat_lit 36)))
                (Nat.shiftLeft v (nat_lit 48))), g4K M Dj c3 v)),
            Nat.lor (Nat.shiftLeft s2 (nat_lit 14)) (Nat.add (Nat.add (Nat.mul (nat_lit 8) k) p) (nat_lit 1)),
            s2)) (nat_lit 8) s,
      s)

@[expose] noncomputable def survK (M Dj BF : Nat → Nat) (H3 H4 t0 t1 t2 : Nat) : Nat :=
  (fun a : Nat → Nat =>
    strictN (Nat.lor (Nat.lor (a (bp (nat_lit 0))) (Nat.shiftLeft (a (bp (nat_lit 1))) (nat_lit 12)))
      (Nat.shiftLeft (a (bp (nat_lit 2))) (nat_lit 24))) fun cs =>
    strictN (maskL M Dj cs (nat_lit 3) (nat_lit 3)) fun m3 =>
    strictN (maskL M Dj cs (nat_lit 3) (nat_lit 4)) fun m4 =>
    foldN (nat_lit 720) (fun k s => stepK M Dj H3 H4 m3 m4 cs a k (BF k) s) (nat_lit 0))
  (fun x => ap t0 (ap t1 (ap t2 x)))

@[expose] noncomputable def blockK (T D M BF H K : Nat → Nat) (j n : Nat) : Bool :=
  strictB (K n) fun row =>
  strictB (T (fld(row, nat_lit 0, nat_lit 65535))) fun t0 =>
  strictB (T (fld(row, nat_lit 16, nat_lit 65535))) fun t1 =>
  strictB (T (fld(row, nat_lit 32, nat_lit 65535))) fun t2 =>
  strictB (H j) fun h =>
  Nat.beq (survK M (fun e => D (Nat.add (Nat.mul (nat_lit 27) j) e)) BF
      (fld(h, nat_lit 0, Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 256)) (nat_lit 1)))
      (Nat.shiftRight h (nat_lit 256)) t0 t1 t2)
    (Nat.shiftRight row (nat_lit 48))

end CFSG.KC.Fi22Twist

end
