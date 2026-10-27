module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.B3M

open CFSG.KC.Loop

universe u v

@[expose] noncomputable def letB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def allN (m : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => bAnd(f i, ih)) m

@[expose] noncomputable def anyN (m : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => bIf(f i, true, ih)) m

@[expose] noncomputable def sumN (m : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i ih => Nat.add (f i) ih) m

@[expose] noncomputable def orN (m : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i ih => Nat.lor (f i) ih) m

@[expose] noncomputable def lenL {α : Type u} (L : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.add ih 1) L

@[expose] noncomputable def lget {α : Type u} (L : List α) (i : Nat) (d : α) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun x _ ih i => Nat.rec (motive := fun _ => α) x (fun j _ => ih j) i) L i

@[expose] noncomputable def allL {α : Type u} (L : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) L

@[expose] noncomputable def orL {α : Type u} (L : List α) (f : α → Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.lor (f x) ih) L

@[expose] noncomputable def allI {α : Type u} (L : List α) (f : Nat → α → Bool) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => letB i (fun i => bAnd(f i x, ih (Nat.add i 1)))) L 0

@[expose] noncomputable def all2 {α : Type u} {β : Type v} (X : List α) (Y : List β) (dy : β)
    (f : Nat → α → β → Bool) : Bool :=
  List.rec (motive := fun _ => Nat → List β → Bool) (fun _ _ => true)
    (fun x _ ih i Y => letB i (fun i =>
      List.rec (motive := fun _ => Bool) (bAnd(f i x dy, ih (Nat.add i 1) []))
        (fun y Y' _ => bAnd(f i x y, ih (Nat.add i 1) Y')) Y)) X 0 Y

@[expose] noncomputable def packL (w : Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.lor x (Nat.shiftLeft ih w)) L

@[expose] noncomputable def ones (w : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 w) 1

@[expose] noncomputable def one (i : Nat) : Nat := Nat.shiftLeft 1 i

@[expose] noncomputable def ent (X w i : Nat) : Nat := fld(X, Nat.mul w i, ones w)

@[expose] noncomputable def bit (X i : Nat) : Bool := Nat.beq (fld(X, i, 1)) 1

@[expose] noncomputable def subM (A B : Nat) : Bool := Nat.beq (Nat.land A B) A

@[expose] noncomputable def beqB (a b : Bool) : Bool := bIf(a, b, bIf(b, false, true))

@[expose] def bpT : Nat :=
  0x8776766576656554766565546554544376656554655454436554544354434332766565546554544365545443544343326554544354434332544343324332322176656554655454436554544354434332655454435443433254434332433232216554544354434332544343324332322154434332433232214332322132212110

@[expose] noncomputable def chkBP : Bool :=
  allN 256 (fun i => Nat.beq (ent bpT 4 i) (sumN 8 (fun j => nIf(bit i j, 1, 0))))

@[expose] noncomputable def popc (nb X : Nat) : Nat := sumN nb (fun j => ent bpT 4 (ent X 8 j))

@[expose] noncomputable def factN (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 1 (fun i ih => Nat.mul (Nat.add i 1) ih) n

@[expose] noncomputable def pt (t i : Nat) : Nat := fld(t, Nat.mul 3 i, 7)

@[expose] noncomputable def pmul (n a b : Nat) : Nat :=
  sumN n (fun i => Nat.shiftLeft (pt a (pt b i)) (Nat.mul 3 i))

@[expose] noncomputable def pinv (n a : Nat) : Nat :=
  sumN n (fun i => Nat.shiftLeft i (Nat.mul 3 (pt a i)))

@[expose] noncomputable def pid (n : Nat) : Nat := sumN n (fun i => Nat.shiftLeft i (Nat.mul 3 i))

@[expose] noncomputable def pswap (n a b : Nat) : Nat :=
  sumN n (fun i => Nat.shiftLeft (nIf(Nat.beq i a, b, nIf(Nat.beq i b, a, i))) (Nat.mul 3 i))

@[expose] noncomputable def isPerm (n a : Nat) : Bool :=
  bAnd(Nat.blt a (one (Nat.mul 3 n)), Nat.beq (orN n (fun i => one (pt a i))) (ones n))

@[expose] noncomputable def supp (n a : Nat) : Nat :=
  sumN n (fun i => nIf(Nat.beq (pt a i) i, 0, 1))

@[expose] noncomputable def evenP (n a : Nat) : Bool :=
  Nat.beq (Nat.mod (sumN n (fun i => sumN i (fun j => nIf(Nat.blt (pt a i) (pt a j), 1, 0)))) 2) 0

@[expose] noncomputable def actV (n t w : Nat) : Nat :=
  orN n (fun i => nIf(bit w i, one (pt t i), 0))

@[expose] noncomputable def a0gen (n i : Nat) : Nat :=
  nIf(Nat.beq i 0, pmul n (pswap n 0 1) (pswap n 2 3),
    nIf(Nat.beq i 1, pmul n (pswap n 0 2) (pswap n 1 3),
      pswap n (Nat.mul 2 i) (Nat.add (Nat.mul 2 i) 1)))

@[expose] noncomputable def t12 (n : Nat) : Nat := pmul n (pswap n 0 1) (pswap n 2 3)

structure Dat where
  n : Nat
  nT : Nat
  e : Nat
  m : Nat
  iw : Nat
  TN : Nat
  mtN : Nat
  CN : Nat
  DN : Nat
  Db : List (List Nat)
  nD : Nat
  ext : List (List (Nat × Nat))
  WN : Nat
  FN : Nat
  Am : List (List Nat)
  A0 : List Nat
  nmw : List Nat
  dtw : List (Nat × Nat)
  S5 : List Nat
  ch5 : List (Nat × Nat × Nat)
  FV : List (List Nat)
  JU : List Nat
  JS : List (List Nat)
  Jch : List (List (Nat × Nat × Nat))
  cov : List (List (List Nat))

namespace Dat

variable (d : Dat)

@[expose] noncomputable def tab (i : Nat) : Nat := ent d.TN (Nat.mul 3 d.n) i

@[expose] noncomputable def row (i : Nat) : Nat := ent d.mtN (Nat.mul d.iw d.nT) i

@[expose] noncomputable def mt (i j : Nat) : Nat := ent (d.row i) d.iw j

@[expose] noncomputable def cen (i : Nat) : Nat := ent d.CN d.nT i

@[expose] noncomputable def dm (j : Nat) : Nat := ent d.DN d.nT j

@[expose] noncomputable def nb : Nat := Nat.div (Nat.add d.nT 7) 8

@[expose] noncomputable def vb : Nat := Nat.shiftRight (one d.n) 3

@[expose] noncomputable def h : Nat := Nat.div d.n 2

@[expose] noncomputable def wM (k : Nat) : Nat := ent d.WN (one d.n) k

@[expose] noncomputable def fM (k x : Nat) : Nat := ent d.FN (one d.n) (Nat.add (Nat.mul k d.nT) x)

@[expose] noncomputable def invM : Nat :=
  orN d.nT (fun s => nIf(bAnd(Nat.blt 0 s, Nat.beq (d.mt s s) 0), one s, 0))

@[expose] noncomputable def nm (i : Nat) : Nat := d.dm (lget d.nmw i 0)

@[expose] noncomputable def dcM : Nat := d.nm (Nat.sub d.h 1)

@[expose] noncomputable def spanP (b : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun s c P => strictN P (fun P => strictN (d.row s) (fun r => strictN (one (lenL c)) (fun z =>
      Nat.lor P (Nat.shiftLeft (orN z (fun x => Nat.shiftLeft (ent r d.iw (ent P d.iw x))
        (Nat.mul d.iw x))) (Nat.mul d.iw z)))))) b

@[expose] noncomputable def spanM (b : List Nat) : Nat :=
  strictN (d.spanP b) (fun P => orN (one (lenL b)) (fun x => one (ent P d.iw x)))

@[expose] noncomputable def basisOK (inv : Nat) (b : List Nat) : Bool :=
  allL b (fun s => bAnd(bit inv s, allL b (fun t => bit (d.cen s) t)))

@[expose] noncomputable def evenPart (M : Nat) : Nat :=
  orN d.nT (fun x => nIf(bAnd(bit M x, evenP d.n (d.tab x)), one x, 0))

@[expose] noncomputable def dtM : Nat :=
  strictN d.invM (fun inv =>
    orN d.nT (fun x => nIf(bAnd(bit inv x, Nat.beq (supp d.n (d.tab x)) 4), one x, 0)))

@[expose] noncomputable def closOK (S : List Nat) (ch : List (Nat × Nat × Nat)) (J : Nat) : Bool :=
  letB (orL S one) (fun SM =>
  bAnd(bit J 0,
  bAnd(subM SM J,
  bAnd(allL S (fun s => letB (d.row s) (fun r =>
      allN d.nT (fun x => bIf(bit J x, bit J (ent r d.iw x), true)))),
    Nat.beq (List.rec (motive := fun _ => Nat → Nat) (fun A => A)
      (fun c _ ih A => strictN A (fun A =>
        nIf(bAnd(bit SM c.2.1, bAnd(bit A c.2.2, Nat.beq (d.mt c.2.1 c.2.2) c.1)),
          ih (Nat.lor A (one c.1)), 0))) ch 1) J))))

end Dat

@[expose] noncomputable def chkTM (d : Dat) : Bool :=
  bAnd(Nat.beq d.nT (one d.e),
  bAnd(Nat.beq (factN d.n) (Nat.mul (one d.e) d.m),
  bAnd(Nat.beq (Nat.mod d.m 2) 1,
  bAnd(Nat.beq (d.tab 0) (pid d.n),
    allN d.nT (fun i => letB (d.tab i) (fun a =>
      bAnd(isPerm d.n a,
      bAnd(allN i (fun j => bIf(Nat.beq (d.tab j) a, false, true)),
        letB (d.row i) (fun r =>
          bAnd(Nat.beq (orN d.nT (fun j => one (ent r d.iw j))) (ones d.nT),
            allN d.nT (fun j => Nat.beq (pmul d.n a (d.tab j)) (d.tab (ent r d.iw j)))))))))))))

@[expose] noncomputable def eaOK (d : Dat) (inv j : Nat) (b : List Nat) (w : List (Nat × Nat)) :
    Bool :=
  letB (d.dm j) (fun M => bAnd(d.basisOK inv b, letB (d.spanP b) (fun P =>
    letB (one (lenL b)) (fun z =>
    bAnd(Nat.beq (orN z (fun x => one (ent P d.iw x))) M,
    bAnd(Nat.beq (popc d.nb M) z,
      letB (Nat.land inv (Nat.land (Nat.xor (ones d.nT) M)
          (List.rec (motive := fun _ => Nat) (ones d.nT) (fun x _ ih => Nat.land (d.cen x) ih) b)))
        (fun Q => bAnd(Nat.beq (orL w (fun p => one p.1)) Q,
          allL w (fun p => bAnd(bit Q p.1, bAnd(Nat.blt p.2 d.nD, letB (d.row p.1) (fun r =>
            Nat.beq (d.dm p.2)
              (Nat.lor M (orN z (fun x => one (ent r d.iw (ent P d.iw x)))))))))))))))))

@[expose] noncomputable def chkEAM (d : Dat) : Bool :=
  letB d.invM (fun inv =>
  bAnd(allN d.nT (fun i => letB (d.row i) (fun r => Nat.beq (d.cen i)
      (orN d.nT (fun j => nIf(Nat.beq (ent r d.iw j) (d.mt j i), one j, 0))))),
  bAnd(Nat.beq (d.dm 0) 1,
  bAnd(Nat.beq (lenL d.Db) d.nD,
  bAnd(Nat.beq (lenL d.ext) d.nD,
    all2 d.Db d.ext [] (fun j b w => eaOK d inv j b w))))))

@[expose] noncomputable def chkNamedM (d : Dat) : Bool :=
  bAnd(Nat.beq (lenL d.Am) d.h,
  bAnd(allI d.Am (fun m b => bAnd(Nat.beq (lenL b) (Nat.add m 1),
      allI b (fun i x => Nat.beq (d.tab x) (pswap d.n (Nat.mul 2 i) (Nat.add (Nat.mul 2 i) 1))))),
  bAnd(Nat.beq (lenL d.A0) d.h,
  bAnd(allI d.A0 (fun i x => Nat.beq (d.tab x) (a0gen d.n i)),
  bAnd(Nat.beq (lenL d.nmw) (Nat.add d.h 2),
  bAnd(allL d.nmw (fun j => Nat.blt j d.nD),
  bAnd(allI d.Am (fun m b => bAnd(Nat.beq (d.spanM b) (d.nm m),
      Nat.beq (popc d.nb (d.nm m)) (one (Nat.add m 1)))),
  bAnd(Nat.beq (d.spanM d.A0) (d.nm d.h),
  bAnd(Nat.beq (popc d.nb (d.nm d.h)) (one d.h),
  bAnd(Nat.beq (d.evenPart d.dcM) (d.nm (Nat.add d.h 1)),
  bAnd(Nat.beq (supp d.n (t12 d.n)) 4,
    letB d.dtM (fun DT => bAnd(Nat.beq (orL d.dtw (fun p => one p.1)) DT,
      allL d.dtw (fun p => bAnd(isPerm d.n p.2, bAnd(bit DT p.1,
        Nat.beq (pmul d.n p.2 (t12 d.n)) (pmul d.n (d.tab p.1) p.2)))))))))))))))))

@[expose] noncomputable def rkOK (FVP pw j r s : Nat) : Bool :=
  Nat.beq (Nat.mul (ent FVP 16 j) (one s)) (Nat.mul (one r) pw)

@[expose] noncomputable def caseOf (n k : Nat) : Nat :=
  nIf(bIf(Nat.beq (Nat.mod n 2) 1, true, Nat.beq (Nat.mod k 2) 0), 0,
    nIf(bAnd(Nat.beq n 8, Nat.beq k 3), 2, 1))

@[expose] noncomputable def inW (k w : Nat) : Bool :=
  bIf(Nat.beq (Nat.mod k 2) 0, true, Nat.beq (Nat.mod (ent bpT 4 w) 2) 0)

@[expose] noncomputable def inN (n k x : Nat) : Bool :=
  bIf(Nat.beq x 0, true, bAnd(Nat.ble 2 k, Nat.beq x (ones n)))

namespace Dat

variable (d : Dat)

@[expose] noncomputable def rowsOK (inv k : Nat) : Bool :=
  bAnd(Nat.beq (d.wM k) (orN (one d.n) (fun w => nIf(inW k w, one w, 0))),
    allN d.nT (fun x => bIf(bit inv x, letB (d.tab x) (fun t => Nat.beq (d.fM k x)
      (orN (one d.n) (fun w => nIf(inN d.n k (Nat.xor (actV d.n t w) w), one w, 0)))), true)))

@[expose] noncomputable def cntM (k W : Nat) (b : List Nat) : Nat :=
  popc d.vb (List.rec (motive := fun _ => Nat) W (fun g _ ih => Nat.land (d.fM k g) ih) b)

@[expose] noncomputable def offM (FVP : Nat) : Nat :=
  orN d.nD (fun j => nIf(letB (d.dm j) (fun M => letB (ent FVP 16 j) (fun f =>
    bAnd(bIf(Nat.beq M 1, false, true),
      allN d.nD (fun c => bIf(subM (d.dm c) M, Nat.ble (ent FVP 16 c) f, true))))), one j, 0))

@[expose] noncomputable def e8 (M : Nat) : Bool :=
  bAnd(Nat.beq (popc d.nb M) 8,
  bAnd(allN d.nT (fun x => bIf(bit M x, evenP d.n (d.tab x), true)),
    Nat.beq (orN d.nT (fun x => nIf(bit M x, one (pt (d.tab x) 0), 0))) (ones d.n)))

@[expose] noncomputable def repP (c M : Nat) : Bool :=
  bIf(anyN d.h (fun i => Nat.beq M (d.nm i)), true,
  bIf(Nat.beq c 0, false,
  bIf(Nat.beq M (d.nm (Nat.add d.h 1)), true,
  bIf(Nat.beq M (d.nm d.h), true,
  bIf(bAnd(subM M d.dcM, bAnd(Nat.beq (Nat.mul 2 (popc d.nb M)) (popc d.nb d.dcM),
      bIf(Nat.beq M (d.nm (Nat.add d.h 1)), false, true))), true,
    bAnd(Nat.beq c 2, d.e8 M))))))

@[expose] noncomputable def covOK (OM RM : Nat) (cv : List (List Nat)) : Bool :=
  bAnd(Nat.beq (orL cv (fun t => one (lget t 0 0))) OM,
    allL cv (fun t => letB (lget t 0 0) (fun c => letB (lget t 1 0) (fun r =>
      letB (lget t 2 0) (fun g =>
      bAnd(bit OM c, bAnd(bit RM r, bAnd(isPerm d.n g,
      bAnd(Nat.beq (popc d.nb (d.dm r)) (popc d.nb (d.dm c)),
        letB (pinv d.n g) (fun gi => letB (d.dm c) (fun MC =>
          allL (lget d.Db r []) (fun b => letB (pmul d.n (pmul d.n g (d.tab b)) gi) (fun p =>
            anyN d.nT (fun y => bAnd(bit MC y, Nat.beq (d.tab y) p)))))))))))))))

@[expose] noncomputable def ranksOK (c FVP pw : Nat) : Bool :=
  bIf(Nat.beq c 0,
    allN d.h (fun i => rkOK FVP pw (lget d.nmw i 0) (Nat.add i 1) (Nat.add i 1)),
  bAnd(allN d.h (fun i => rkOK FVP pw (lget d.nmw i 0) (Nat.add i 1)
      (nIf(Nat.beq (Nat.add i 1) d.h, Nat.sub d.h 1, Nat.add i 1))),
  bAnd(rkOK FVP pw (lget d.nmw d.h 0) d.h d.h,
    bIf(Nat.beq c 2, allN d.nD (fun j => bIf(d.e8 (d.dm j), rkOK FVP pw j 3 3, true)), true))))

@[expose] noncomputable def qOK (FVP RK pw RM snum sden : Nat) : Bool :=
  bAnd(allN d.nD (fun j => bIf(bit RM j, letB (ent RK 4 j) (fun r => bAnd(Nat.blt 0 r,
      anyN (Nat.add d.n 1) (fun s => bAnd(rkOK FVP pw j r s,
        Nat.ble (Nat.mul snum r) (Nat.mul sden s))))), true)),
    anyN d.nD (fun j => bAnd(bit RM j, letB (ent RK 4 j) (fun r =>
      anyN (Nat.add d.n 1) (fun s => bAnd(rkOK FVP pw j r s,
        Nat.ble (Nat.mul sden s) (Nat.mul snum r)))))))

@[expose] noncomputable def strongOK (OM FVP pw : Nat) : Bool :=
  allN d.nD (fun j => bIf(bit OM j,
    beqB (Nat.blt pw (ent FVP 16 j)) (Nat.beq (d.dm j) d.dcM), true))

@[expose] noncomputable def jOK (k c U : Nat) : Bool :=
  letB (lget d.JU k 0) (fun J =>
  bAnd(d.closOK (lget d.JS k []) (lget d.Jch k []) J,
  bAnd(allL (lget d.JS k []) (fun s => bit U s),
  bAnd(subM U J,
    bIf(Nat.beq c 0, Nat.beq J d.dcM,
    bIf(Nat.beq c 2, Nat.beq J (ones d.nT),
      letB (Nat.lor d.dcM d.dtM) (fun DD =>
        bAnd(d.closOK d.S5 d.ch5 J, bAnd(subM (orL d.S5 one) DD, subM DD J)))))))))

end Dat

@[expose] noncomputable def chkModM (d : Dat) (k : Nat) : Bool :=
  letB d.invM (fun inv => letB (d.wM k) (fun W => letB (popc d.vb W) (fun pw =>
  letB (caseOf d.n k) (fun c =>
  bAnd(d.rowsOK inv k,
  bAnd(Nat.beq (lenL (lget d.FV k [])) d.nD,
  bAnd(all2 d.Db (lget d.FV k []) 0 (fun _ b fv => bAnd(Nat.blt fv 65536,
      Nat.beq fv (Nat.mul (one (lenL b)) (d.cntM k W b)))),
  letB (packL 16 (lget d.FV k [])) (fun FVP =>
  letB (List.rec (motive := fun _ => Nat) 0
      (fun b _ ih => Nat.lor (lenL b) (Nat.shiftLeft ih 4)) d.Db) (fun RK =>
  letB (d.offM FVP) (fun OM =>
  letB (orN d.nD (fun j => nIf(bit OM j, d.dm j, 0))) (fun U =>
  letB (orN d.nD (fun j => nIf(d.repP c (d.dm j), one j, 0))) (fun RM =>
  bAnd(subM RM OM,
  bAnd(d.covOK OM RM (lget d.cov k []),
  bAnd(d.jOK k c U,
  bAnd(d.ranksOK c FVP pw,
  bAnd(bIf(Nat.beq c 0, d.qOK FVP RK pw RM 1 1, d.qOK FVP RK pw RM (Nat.sub d.n 2) d.n),
    bIf(Nat.beq c 0, true, d.strongOK OM FVP pw))))))))))))))))))

end CFSG.KC.B3M

end
