module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Data.Kernel.TreeK

public section

namespace CFSG.KC.U52PL

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def mulT : Nat := nat_lit 2625168384

@[expose] noncomputable def mulK (a b : Nat) : Nat :=
  fld(mulT, Nat.mul (nat_lit 2) (Nat.add (Nat.mul (nat_lit 4) a) b), nat_lit 3)

@[expose] noncomputable def f2 (p j : Nat) : Nat := pg (nat_lit 2) (mask (nat_lit 2)) p j

@[expose] noncomputable def mk5 (a b c d e : Nat) : Nat :=
  Nat.add a (Nat.mul (nat_lit 4) (Nat.add b (Nat.mul (nat_lit 4) (Nat.add c
    (Nat.mul (nat_lit 4) (Nat.add d (Nat.mul (nat_lit 4) e)))))))

@[expose] noncomputable def dotK (a b : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (mulK (f2 a 0) (f2 b 0)) (mulK (f2 a 1) (f2 b 1)))
    (mulK (f2 a 2) (f2 b 2))) (mulK (f2 a 3) (f2 b 3))) (mulK (f2 a 4) (f2 b 4))

@[expose] noncomputable def barK (u : Nat) : Nat :=
  mk5 (mulK (f2 u 0) (f2 u 0)) (mulK (f2 u 1) (f2 u 1)) (mulK (f2 u 2) (f2 u 2))
    (mulK (f2 u 3) (f2 u 3)) (mulK (f2 u 4) (f2 u 4))

@[expose] noncomputable def tvK (u v : Nat) : Nat :=
  strictN (dotK (barK u) v) fun s =>
    mk5 (Nat.xor (f2 v 0) (mulK (f2 u 0) s)) (Nat.xor (f2 v 1) (mulK (f2 u 1) s))
      (Nat.xor (f2 v 2) (mulK (f2 u 2) s)) (Nat.xor (f2 v 3) (mulK (f2 u 3) s))
      (Nat.xor (f2 v 4) (mulK (f2 u 4) s))

@[expose] noncomputable def scK (l v : Nat) : Nat :=
  mk5 (mulK l (f2 v 0)) (mulK l (f2 v 1)) (mulK l (f2 v 2)) (mulK l (f2 v 3)) (mulK l (f2 v 4))

@[expose] noncomputable def leadK (p : Nat) : Nat :=
  nIf(Nat.beq (f2 p 0) (nat_lit 0),
    nIf(Nat.beq (f2 p 1) (nat_lit 0),
      nIf(Nat.beq (f2 p 2) (nat_lit 0),
        nIf(Nat.beq (f2 p 3) (nat_lit 0), f2 p 4, f2 p 3), f2 p 2), f2 p 1), f2 p 0)

@[expose] noncomputable def normK (p : Nat) : Nat :=
  strictN (leadK p) fun l => scK (mulK l l) p

@[expose] noncomputable def ptNorm (p : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight p (nat_lit 10)) (nat_lit 0), Nat.beq (leadK p) (nat_lit 1))

@[expose] noncomputable def ptsK (F : Nat → Nat) : Bool :=
  bAnd(allN (nat_lit 165) fun i => ptNorm (F i),
    CFSG.KC.TreeK.distinctK (nat_lit 8) ((List.range (nat_lit 165)).map F))

@[expose] noncomputable def f8 (q a : Nat) : Nat := pg (nat_lit 8) (mask (nat_lit 8)) q a

@[expose] noncomputable def lnInc (q : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight q (nat_lit 40)) (nat_lit 0),
    bAnd(Nat.blt (f8 q 0) (f8 q 1), bAnd(Nat.blt (f8 q 1) (f8 q 2),
      bAnd(Nat.blt (f8 q 2) (f8 q 3), bAnd(Nat.blt (f8 q 3) (f8 q 4),
        Nat.blt (f8 q 4) (nat_lit 165))))))

@[expose] noncomputable def lnsK (L : Nat → Nat) : Bool :=
  bAnd(allN (nat_lit 297) fun l => lnInc (L l),
    CFSG.KC.TreeK.distinctK (nat_lit 9) ((List.range (nat_lit 297)).map L))

@[expose] noncomputable def any5 (f : Nat → Nat) (x : Nat) : Bool :=
  bIf(Nat.beq (f 0) x, true, bIf(Nat.beq (f 1) x, true, bIf(Nat.beq (f 2) x, true,
    bIf(Nat.beq (f 3) x, true, Nat.beq (f 4) x))))

@[expose] noncomputable def genPt (G U F : Nat → Nat) (k i : Nat) : Bool :=
  strictB (pg (nat_lit 9) (mask (nat_lit 9)) (G k) i) fun j =>
    bAnd(Nat.blt j (nat_lit 165), Nat.beq (normK (tvK (U k) (F i))) (F j))

@[expose] noncomputable def genLn (G L : Nat → Nat) (k l : Nat) : Bool :=
  strictB (pg (nat_lit 9) (mask (nat_lit 9)) (G k) (Nat.add (nat_lit 165) l)) fun t =>
    bAnd(Nat.ble (nat_lit 165) t, bAnd(Nat.blt t (nat_lit 462),
      strictB (L (Nat.sub t (nat_lit 165))) fun q' => strictB (L l) fun q =>
        bAnd(allN (nat_lit 5) fun a => any5 (f8 q') (pg (nat_lit 9) (mask (nat_lit 9)) (G k) (f8 q a)),
          allN (nat_lit 5) fun b =>
            any5 (fun a => pg (nat_lit 9) (mask (nat_lit 9)) (G k) (f8 q a)) (f8 q' b))))

@[expose] noncomputable def gensK (G U F L : Nat → Nat) : Bool :=
  bAnd(allN (nat_lit 6) fun k => allN (nat_lit 165) fun i => genPt G U F k i,
    allN (nat_lit 6) fun k => allN (nat_lit 297) fun l => genLn G L k l)

@[expose] noncomputable def isoK (U : Nat → Nat) : Bool :=
  allN (nat_lit 6) fun k =>
    bAnd(Nat.beq (Nat.shiftRight (U k) (nat_lit 10)) (nat_lit 0),
      Nat.beq (dotK (barK (U k)) (U k)) (nat_lit 0))

end CFSG.KC.U52PL

end
