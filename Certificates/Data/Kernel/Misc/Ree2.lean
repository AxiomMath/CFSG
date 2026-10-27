module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Walter.Ree.Bombieri.Subst

public section

namespace CFSG.KC.Misc.Ree2

open CFSG.KC.Loop CFSG.Walter.Ree.Bombieri

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def loopN (n b : Nat) (f : Nat → Nat → Nat) (s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ s => s)
    (fun _ ih a s => strictN (f a s) (ih (Nat.succ a))) n b s

@[expose] noncomputable def allFrom (n b : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih a => bAnd(f a, ih (Nat.succ a))) n b

@[expose] noncomputable def zech (ZT d : Nat) : Nat :=
  fld(ZT, Nat.mul (nat_lit 15) d, nat_lit 32767)

@[expose] noncomputable def mulL (q1 a b : Nat) : Nat :=
  nIf(Nat.beq a q1, q1, nIf(Nat.beq b q1, q1, Nat.mod (Nat.add a b) q1))

@[expose] noncomputable def addL (q1 ZT a b : Nat) : Nat :=
  nIf(Nat.beq a q1, b, nIf(Nat.beq b q1, a,
    strictN (zech ZT (Nat.mod (Nat.sub (Nat.add b q1) a) q1)) (fun z =>
      nIf(Nat.beq z q1, q1, Nat.mod (Nat.add a z) q1))))

@[expose] noncomputable def negL (q1 hf a : Nat) : Nat :=
  nIf(Nat.beq a q1, q1, Nat.mod (Nat.add a hf) q1)

@[expose] noncomputable def subL (q1 hf ZT a b : Nat) : Nat := addL q1 ZT a (negL q1 hf b)

@[expose] noncomputable def invL (q1 a : Nat) : Nat := Nat.mod (Nat.sub q1 a) q1

@[expose] noncomputable def powL (q1 a n : Nat) : Nat :=
  nIf(Nat.beq n (nat_lit 0), nat_lit 0, nIf(Nat.beq a q1, q1, Nat.mod (Nat.mul a n) q1))

@[expose] noncomputable def resL (q1 hf v : Nat) : Nat :=
  strictN (Nat.mod v (nat_lit 3)) (fun w =>
    nIf(Nat.beq w (nat_lit 0), q1, nIf(Nat.beq w (nat_lit 1), nat_lit 0, hf)))

@[expose] noncomputable def constL (q1 hf : Nat) (c : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun n => resL q1 hf n)
    (fun n => resL q1 hf (Nat.mul (nat_lit 2) (Nat.succ n))) c

@[expose] noncomputable def evalL (q1 hf ZT : Nat) (ρ α : Nat → Nat) (e : PE) : Nat :=
  PE.rec (motive := fun _ => Nat) (fun i => ρ i) (fun k => α k) (fun c => constL q1 hf c)
    (fun _ _ ra rb => strictN ra (fun x => strictN rb (fun y => addL q1 ZT x y)))
    (fun _ _ ra rb => strictN ra (fun x => strictN rb (fun y => subL q1 hf ZT x y)))
    (fun _ _ ra rb => strictN ra (fun x => strictN rb (fun y => mulL q1 x y)))
    (fun _ n ra => strictN ra (fun x => powL q1 x n))
    (fun _ ra => strictN ra (fun x => negL q1 hf x)) e

@[expose] noncomputable def getP (M p : Nat) : Nat :=
  fld(M, Nat.mul (nat_lit 16) p, nat_lit 65535)

@[expose] noncomputable def setP (M p v : Nat) : Nat :=
  strictN (Nat.mul (nat_lit 16) p) (fun o =>
    Nat.add (Nat.sub M (Nat.shiftLeft (fld(M, o, nat_lit 65535)) o)) (Nat.shiftLeft v o))

@[expose] noncomputable def packL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor x (Nat.shiftLeft ih (nat_lit 16))) l

@[expose] noncomputable def lenL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def hornerL (q1 ZT : Nat) (l : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) q1
    (fun a _ ih => strictN ih (fun h => addL q1 ZT a (mulL q1 x h))) l

@[expose] noncomputable def nthL (q1 : Nat) (l : List Nat) (k : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => q1)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun i' _ => ih i') i) l k

@[expose] noncomputable def coefAt (q1 : Nat) (cs : List Nat) (s : Nat) : Nat :=
  nIf(Nat.beq s (nat_lit 0), q1, nthL q1 cs (Nat.sub s (nat_lit 1)))

@[expose] noncomputable def buildM (q1 S : Nat) (cs : List Nat) : Nat :=
  loopN (nat_lit 144) (nat_lit 0) (fun p M =>
    Nat.lor M (Nat.shiftLeft (coefAt q1 cs (fld(S, Nat.mul (nat_lit 5) p, nat_lit 31)))
      (Nat.mul (nat_lit 16) p))) (nat_lit 0)

@[expose] noncomputable def elimStep (q1 hf ZT k M : Nat) : Nat :=
  strictN (invL q1 (getP M (Nat.mul (nat_lit 13) k))) (fun ip =>
  loopN (Nat.sub (nat_lit 11) k) (Nat.succ k) (fun i M =>
    strictN (getP M (Nat.add (Nat.mul (nat_lit 12) i) k)) (fun l =>
    nIf(Nat.beq l q1, M,
      strictN (mulL q1 l ip) (fun lp =>
      loopN (Nat.sub (nat_lit 11) k) (Nat.succ k) (fun j M =>
        strictN (getP M (Nat.add (Nat.mul (nat_lit 12) k) j)) (fun akj =>
        nIf(Nat.beq akj q1, M,
          strictN (Nat.add (Nat.mul (nat_lit 12) i) j) (fun p =>
            setP M p (subL q1 hf ZT (getP M p) (mulL q1 lp akj)))))) M)))) M)

@[expose] noncomputable def detM (q1 hf ZT M : Nat) : Nat :=
  strictN (loopN (nat_lit 12) (nat_lit 0) (fun k M => elimStep q1 hf ZT k M) M) (fun U =>
    nIf(allFrom (nat_lit 12) (nat_lit 0) (fun k =>
        Bool.rec (motive := fun _ => Bool) true false (Nat.beq (getP U (Nat.mul (nat_lit 13) k)) q1)),
      loopN (nat_lit 12) (nat_lit 0) (fun k d => mulL q1 d (getP U (Nat.mul (nat_lit 13) k)))
        (nat_lit 0),
      Nat.succ q1))

@[expose] noncomputable def varsL (q1 z0 z1 z2 z3 y : Nat) (i : Nat) : Nat :=
  nIf(Nat.beq i (nat_lit 0), z0, nIf(Nat.beq i (nat_lit 1), z1, nIf(Nat.beq i (nat_lit 2), z2,
    nIf(Nat.beq i (nat_lit 3), z3, nIf(Nat.beq i (nat_lit 4), y, q1)))))

@[expose] noncomputable def evalList (q1 hf ZT : Nat) (ρ α : Nat → Nat) (l : List PE) :
    List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun e _ ih => evalL q1 hf ZT ρ α e :: ih) l

@[expose] noncomputable def detL (q1 hf ZT S : Nat) (AL CL : List PE) (z0 z1 z2 z3 y : Nat) :
    Nat :=
  strictN (packL (evalList q1 hf ZT (varsL q1 z0 z1 z2 z3 y) (fun _ => q1) AL)) (fun A =>
    detM q1 hf ZT (buildM q1 S (evalList q1 hf ZT (varsL q1 z0 z1 z2 z3 y)
      (fun k => getP A k) CL)))

open PE in
@[expose] def atomL : List PE :=
  [1 + var 1 * var 0 ^ 2, 1 + var 2 * var 1 ^ 2, 1 + var 3 * var 2 ^ 2,
    var 1 * var 0 * var 4 - (1 + var 1 * var 0 ^ 2),
    var 2 * var 1 * (1 + var 1 * var 0 ^ 2) - (1 + var 2 * var 1 ^ 2) * var 4 ^ 2,
    (1 + var 2 * var 1 ^ 2) * var 4 ^ 4,
    var 3 * var 2 * ((1 + var 2 * var 1 ^ 2) * var 4 ^ 4) -
      (1 + var 3 * var 2 ^ 2) * (1 + var 1 * var 0 ^ 2) ^ 2]

@[expose] def coefL : List PE :=
  [Elim.b1, Elim.d1, Elim.e1, Elim.f1, Elim.a0, Elim.b0, Elim.c0, Elim.e0, Elim.b3, Elim.d3,
    Elim.e3, Elim.f3, Elim.a2, Elim.b2, Elim.c2, Elim.e2]

@[expose] def shapeL : Nat :=
  1790129496246605669504885069268096873815335309510985420355601970581085379022462595983213415851398954821971405156416164110134035350625167412221308682891201137974629909034513223621013267665128435643522624181982352900097

@[expose] noncomputable def mpP (x : Nat) : Nat := Nat.land x (nat_lit 65535)

@[expose] noncomputable def mpN (x : Nat) : Nat := Nat.shiftRight x (nat_lit 16)

@[expose] noncomputable def mpOf (p n : Nat) : Nat := Nat.lor p (Nat.shiftLeft n (nat_lit 16))

@[expose] noncomputable def addMP (x y : Nat) : Nat :=
  strictN (Nat.xor (Nat.lor (mpP x) (mpN y)) (Nat.lor (mpN x) (mpP y))) (fun t =>
    mpOf (Nat.xor (Nat.lor (mpN x) (mpN y)) t) (Nat.xor (Nat.lor (mpP x) (mpP y)) t))

@[expose] noncomputable def negMP (x : Nat) : Nat := mpOf (mpN x) (mpP x)

@[expose] noncomputable def mulXMP (m F x : Nat) : Nat :=
  strictN (mpOf (Nat.shiftLeft (mpP x) (nat_lit 1)) (Nat.shiftLeft (mpN x) (nat_lit 1))) (fun y =>
    nIf(Nat.blt (nat_lit 0) (Nat.land (mpP y) (Nat.shiftLeft (nat_lit 1) m)), addMP y (negMP F),
      nIf(Nat.blt (nat_lit 0) (Nat.land (mpN y) (Nat.shiftLeft (nat_lit 1) m)), addMP y F, y)))

@[expose] noncomputable def mulByG (m F g dg x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun j ih acc => strictN (mulXMP m F acc) (fun a =>
      strictN (nIf(Nat.blt (nat_lit 0) (Nat.land (mpP g) (Nat.shiftLeft (nat_lit 1) j)),
        addMP a x, nIf(Nat.blt (nat_lit 0) (Nat.land (mpN g) (Nat.shiftLeft (nat_lit 1) j)),
          addMP a (negMP x), a))) ih))
    (Nat.succ dg) (nat_lit 0)

@[expose] noncomputable def etAt (ET e : Nat) : Nat :=
  fld(ET, Nat.mul (nat_lit 32) e, nat_lit 4294967295)

@[expose] noncomputable def chainOK (m F g dg q1 ET e₀ n : Nat) : Bool :=
  allFrom n e₀ (fun e => Nat.beq (mulByG m F g dg (etAt ET e))
    (etAt ET (Nat.mod (Nat.succ e) q1)))

@[expose] noncomputable def zechOK (q1 ET ZT d₀ n : Nat) : Bool :=
  allFrom n d₀ (fun d => strictB (zech ZT d) (fun z => strictB (addMP (nat_lit 1) (etAt ET d))
    (fun v => bIf(Nat.beq z q1, Nat.beq v (nat_lit 0),
      bAnd(Nat.blt z q1, Nat.beq (etAt ET z) v)))))

@[expose] noncomputable def headOK (m F g dg q1 hf ET ZT D : Nat) : Bool :=
  bAnd(Nat.ble (nat_lit 2) m, bAnd(Nat.blt m (nat_lit 16),
  bAnd(Nat.beq q1 (Nat.sub (Nat.pow (nat_lit 3) m) (nat_lit 1)),
  bAnd(Nat.beq hf (Nat.div q1 (nat_lit 2)),
  bAnd(Nat.beq (Nat.land (mpP F) (mpN F)) (nat_lit 0),
  bAnd(Nat.beq (Nat.shiftRight (mpP F) m) (nat_lit 1),
  bAnd(Nat.beq (Nat.shiftRight (mpN F) m) (nat_lit 0),
  bAnd(Nat.beq (Nat.land (mpP g) (mpN g)) (nat_lit 0),
  bAnd(Nat.blt dg m,
  bAnd(Nat.beq (Nat.shiftRight (Nat.lor (mpP g) (mpN g)) (Nat.succ dg)) (nat_lit 0),
  bAnd(Nat.beq (etAt ET (nat_lit 0)) (nat_lit 1),
  bAnd(Nat.beq (etAt ET hf) (mpOf (nat_lit 0) (nat_lit 1)),
  bAnd(Nat.ble D hf,
    allFrom D (nat_lit 1) (fun j =>
      Bool.rec (motive := fun _ => Bool) true false
        (Nat.beq (zech ZT (Nat.mod (Nat.add j hf) q1)) q1)))))))))))))))

@[expose] noncomputable def lanesOf (m x : Nat) : Nat :=
  loopN (Nat.succ m) (nat_lit 0) (fun i L => Nat.lor L (Nat.shiftLeft
    (Nat.add (fld(mpP x, i, nat_lit 1)) (Nat.mul (nat_lit 2) (fld(mpN x, i, nat_lit 1))))
    (Nat.mul (nat_lit 32) i))) (nat_lit 0)

@[expose] noncomputable def cpt (q1 : Nat) (W : List Nat) (k lam : Nat) (neg : Bool) (j : Nat) :
    Nat :=
  powL q1 (nthL q1 W (substIdx k neg j)) (Nat.pow (nat_lit 3) (substExp k lam neg j))

@[expose] noncomputable def cvars (q1 c0 c1 c2 c3 c4 : Nat) (i : Nat) : Nat :=
  varsL q1 c0 c1 c2 c3 c4 i

@[expose] noncomputable def qOK (q1 hf ZT c0 c1 c2 c3 c4 : Nat) : Bool :=
  bAnd(Bool.rec (motive := fun _ => Bool) true false
    (Nat.beq (evalL q1 hf ZT (cvars q1 c0 c1 c2 c3 c4) (fun _ => q1) (Elim.qExpr 0)) q1),
  bAnd(Bool.rec (motive := fun _ => Bool) true false
    (Nat.beq (evalL q1 hf ZT (cvars q1 c0 c1 c2 c3 c4) (fun _ => q1) (Elim.qExpr 1)) q1),
    Bool.rec (motive := fun _ => Bool) true false
    (Nat.beq (evalL q1 hf ZT (cvars q1 c0 c1 c2 c3 c4) (fun _ => q1) (Elim.qExpr (-1))) q1)))

@[expose] noncomputable def interpOK (q1 hf ZT S : Nat) (AL CL : List PE)
    (c0 c1 c2 c3 c4 : Nat) (xs p p' : List Nat) (i₀ n : Nat) : Bool :=
  allFrom n i₀ (fun i => strictB (nthL q1 xs i) (fun x => bAnd(
    Nat.beq (detL q1 hf ZT S AL CL c0 c1 c2 c3 x) (hornerL q1 ZT p x),
    Nat.beq (detL q1 hf ZT S AL CL c1 c2 c3 c4 x) (hornerL q1 ZT p' x))))

@[expose] noncomputable def ptsOK (D R : Nat) (xs : List Nat) : Bool :=
  bAnd(Nat.beq (lenL xs) (Nat.succ D),
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun x _ ih lo => bAnd(Nat.ble lo x, bAnd(Nat.blt x R, ih (Nat.succ x)))) xs (nat_lit 0))

@[expose] noncomputable def p1Pack (q1 D ζ : Nat) (p' : List Nat) : Nat :=
  loopN (Nat.succ (Nat.add D D)) (nat_lit 0) (fun n P =>
    Nat.lor P (Nat.shiftLeft (nIf(Nat.beq (Nat.mod n (nat_lit 2)) (nat_lit 0),
      strictN (Nat.sub D (Nat.div n (nat_lit 2))) (fun j => mulL q1 (nthL q1 p' j) (powL q1 ζ j)),
      q1)) (Nat.mul (nat_lit 16) n))) (nat_lit 0)

@[expose] noncomputable def logsOK (q1 : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(Nat.ble x q1, ih)) l

@[expose] noncomputable def convAt (q1 ZT A B n lo hi : Nat) : Nat :=
  loopN (Nat.sub (Nat.succ hi) lo) lo (fun i acc =>
    addL q1 ZT acc (mulL q1 (getP A i) (getP B (Nat.sub n i)))) q1

@[expose] noncomputable def bezCoef (q1 ZT D Sp Pp Tp P1 ls lt n : Nat) : Nat :=
  strictN (convAt q1 ZT Sp Pp n (Nat.sub n D) (Nat.min n (Nat.sub ls (nat_lit 1)))) (fun a =>
    strictN (convAt q1 ZT Tp P1 n (Nat.sub n (Nat.add D D)) (Nat.min n (Nat.sub lt (nat_lit 1))))
      (fun b => addL q1 ZT a b))

@[expose] noncomputable def bezRange (q1 ZT D Sp Pp Tp P1 ls lt g0 n₀ k : Nat) : Bool :=
  allFrom k n₀ (fun n => Nat.beq (bezCoef q1 ZT D Sp Pp Tp P1 ls lt n)
    (nIf(Nat.beq n (nat_lit 0), g0, q1)))

@[expose] noncomputable def bezOK (q1 ZT D : Nat) (s p t : List Nat) (P1 g0 n₀ k : Nat) : Bool :=
  strictB P1 (fun P1v => strictB (packL s) (fun Sp => strictB (packL p) (fun Pp =>
    strictB (packL t) (fun Tp => bezRange q1 ZT D Sp Pp Tp P1v (lenL s) (lenL t) g0 n₀ k))))

@[expose] noncomputable def sizeOK (q1 D : Nat) (p p' s t : List Nat) (g0 : Nat) : Bool :=
  bAnd(Nat.beq (lenL p) (Nat.succ D),
  bAnd(Bool.rec (motive := fun _ => Bool) true false (Nat.beq (nthL q1 p D) q1),
  bAnd(Nat.ble (lenL p') (Nat.succ D),
  bAnd(Nat.ble (lenL s) (Nat.add D D), bAnd(Nat.blt (nat_lit 0) (lenL s),
  bAnd(Nat.ble (lenL t) D, bAnd(Nat.blt (nat_lit 0) (lenL t),
  bAnd(Nat.blt g0 q1, bAnd(Nat.blt q1 (nat_lit 65535),
  bAnd(logsOK q1 p, bAnd(logsOK q1 p', bAnd(logsOK q1 s, logsOK q1 t))))))))))))

end CFSG.KC.Misc.Ree2

end
