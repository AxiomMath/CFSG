module

public import Certificates.Data.Kernel.Misc.RuScanL
public import Certificates.Data.Kernel.Misc.RuScanB

public section

namespace CFSG.KC.Misc.RuScan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuInv

@[expose] noncomputable def tIf (T m j v : Nat) : Nat :=
  nIf(Nat.beq (Nat.land (Nat.shiftRight m j) (nat_lit 1)) (nat_lit 1), apP T v, v)

@[expose] noncomputable def walkE (ys : List Nat) (T m n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun u => tIf T m (nat_lit 0) u)
    (fun n ih u => ih (yAp ys (tIf T m (Nat.succ n) u))) n

@[expose] noncomputable def cAp (XP : Nat → Nat) (g o v : Nat) : Nat :=
  apP (XP (Nat.mul (nat_lit 2) g))
    (apP (XP o) (apP (XP (Nat.succ (Nat.mul (nat_lit 2) g))) v))

@[expose] noncomputable def prodT (XP : Nat → Nat) (g ob m r : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun b => b)
    (fun r ih b => ih (nIf(Nat.beq (Nat.land (Nat.shiftRight m r) (nat_lit 1)) (nat_lit 1),
      cAp XP g (Nat.add ob r) b, b))) r

@[expose] noncomputable def rk (t : Nat) : Nat :=
  nIf(Nat.beq t 0, nat_lit 3, nIf(Nat.beq t 1, nat_lit 6, nIf(Nat.beq t 2, nat_lit 3,
    nIf(Nat.beq t 3, nat_lit 4, nat_lit 5))))

@[expose] noncomputable def boff (t : Nat) : Nat :=
  nIf(Nat.beq t 0, nat_lit 0, nIf(Nat.beq t 1, nat_lit 3, nIf(Nat.beq t 2, nat_lit 9,
    nIf(Nat.beq t 3, nat_lit 12, nat_lit 16))))

@[expose] noncomputable def elemOK (ys : List Nat) (T : Nat) (Kh XP : Nat → Nat)
    (g ob q ko S Tm r k : Nat) : Bool :=
  allN (nat_lit 4) (fun b =>
    strictB (Kh (Nat.add ko b)) (fun u1 =>
    strictB (Kh (Nat.add ko (Nat.add (Nat.mul (nat_lit 4) (Nat.sub q (nat_lit 1))) b))) (fun uq =>
    strictB (cAp XP g (Nat.add ob k) b) (fun xb =>
    bAnd(Nat.blt u1 (nat_lit 4060), bAnd(Nat.blt uq (nat_lit 4060),
    bAnd(Nat.beq (yAp ys u1) b, bAnd(Nat.beq (yPow ys q uq) b,
    bAnd(Nat.beq (walkE ys T S q uq) xb,
      Nat.beq (yAp ys (cAp XP g (Nat.add ob k) u1)) (prodT XP g ob Tm r b))))))))))

@[expose] noncomputable def candOK (ys : List Nat) (T : Nat) (Kh V XP CT : Nat → Nat)
    (nc go : Nat) (D : Nat → Nat) (l o : Nat) : Bool :=
  strictB (D (Nat.add o (nat_lit 1))) (fun p =>
  strictB (D (Nat.add o (nat_lit 2))) (fun ci =>
  strictB (CT ci) (fun t =>
  strictB (V (Nat.add (Nat.add (nat_lit 64) (Nat.mul (nat_lit 32) l)) (nat_lit 28))) (fun q =>
  strictB (rk t) (fun r =>
  strictB (Nat.add (nat_lit 46) (boff t)) (fun ob =>
  bAnd(kbndK Kh (Nat.mul (nat_lit 32) p) (nat_lit 28),
  bAnd(leafOK ys T Kh V l p,
  bAnd(Nat.blt ci nc,
  bAnd(Nat.blt t (nat_lit 5),
  bAnd(Nat.beq (nIf(Nat.blt t (nat_lit 3), nat_lit 7, nat_lit 5)) q,
    allN r (fun k => elemOK ys T Kh XP (Nat.add go ci) ob q (Nat.mul (nat_lit 32) p)
      (D (Nat.add o (Nat.add (nat_lit 3) (Nat.mul (nat_lit 2) k))))
      (D (Nat.add o (Nat.add (nat_lit 4) (Nat.mul (nat_lit 2) k)))) r k))))))))))))

@[expose] noncomputable def candC2 (LR TR D Kh V XP CT : Nat → Nat) (nc go H T N dofs lo cnt : Nat) :
    Bool :=
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 0)) (fun o0 =>
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 1)) (fun o1 =>
  strictB (rcnt (LR 1)) (fun c1 =>
  allN cnt (fun d => strictB (Nat.add lo d) (fun l =>
    strictB (Nat.mul (nat_lit 16) (Nat.add dofs l)) (fun o =>
    strictB (D o) (fun i =>
    strictB (TR (Nat.add o0 (Nat.div i c1))) (fun t0 =>
    strictB (TR (Nat.add o1 (Nat.mod i c1))) (fun t1 =>
      bAnd(Nat.blt i N, candOK [H, t0, t1] T Kh V XP CT nc go D l o))))))))))

@[expose] noncomputable def candC3 (LR TR D Kh V XP CT : Nat → Nat) (nc go H T N dofs lo cnt : Nat) :
    Bool :=
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 0)) (fun o0 =>
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 1)) (fun o1 =>
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 2)) (fun o2 =>
  strictB (rcnt (LR 1)) (fun c1 =>
  strictB (rcnt (LR 2)) (fun c2 =>
  allN cnt (fun d => strictB (Nat.add lo d) (fun l =>
    strictB (Nat.mul (nat_lit 16) (Nat.add dofs l)) (fun o =>
    strictB (D o) (fun i =>
    strictB (Nat.div i c2) (fun q =>
    strictB (TR (Nat.add o0 (Nat.div q c1))) (fun t0 =>
    strictB (TR (Nat.add o1 (Nat.mod q c1))) (fun t1 =>
    strictB (TR (Nat.add o2 (Nat.mod i c2))) (fun t2 =>
      bAnd(Nat.blt i N, candOK [H, t0, t1, t2] T Kh V XP CT nc go D l o))))))))))))))

@[expose] noncomputable def gen6 (a b c d e f l : Nat) : Nat :=
  nIf(Nat.beq l 0, a, nIf(Nat.beq l 1, b, nIf(Nat.beq l 2, c, nIf(Nat.beq l 3, d,
    nIf(Nat.beq l 4, e, f)))))

end CFSG.KC.Misc.RuScan

end
