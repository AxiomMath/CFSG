module

public import Certificates.Data.Kernel.SporSch.LyMat
public import Certificates.Data.Kernel.SporSch.Kappa

public section

namespace CFSG.KS.SporSch.LySyl

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def b8 (x j : Nat) : Nat := fld(x, Nat.mul (nat_lit 8) j, nat_lit 255)

@[expose] noncomputable def tmK (MT : Nat → Nat) (i j : Nat) : Nat := b8 (MT i) j

@[expose] noncomputable def lamK (W : Nat → Nat) (k h : Nat) : Nat :=
  fld(W h, Nat.mul (nat_lit 9) k, nat_lit 511)

@[expose] noncomputable def parK (PL : Nat → Nat) (j : Nat) : Nat := Nat.land (PL j) (nat_lit 511)

@[expose] noncomputable def labK (PL : Nat → Nat) (j : Nat) : Nat := Nat.shiftRight (PL j) (nat_lit 9)

@[expose] noncomputable def posK (PL : Nat → Nat) (j : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 6) (parK PL j)) (labK PL j)

@[expose] noncomputable def plOK (W PL : Nat → Nat) (n j : Nat) : Bool :=
  bAnd(bIf(Nat.beq j (nat_lit 0), true,
    bAnd(Nat.blt (parK PL j) j, bAnd(Nat.blt (labK PL j) (nat_lit 6),
    bAnd(Nat.beq (lamK W (labK PL j) (parK PL j)) j,
      bIf(Nat.blt (Nat.succ j) n, Nat.blt (posK PL j) (posK PL (Nat.succ j)), true))))),
  allN (nat_lit 6) (fun k => strictB (lamK W k j) (fun x => bAnd(Nat.blt x n,
    bIf(Nat.beq x (nat_lit 0), true,
      Nat.ble (posK PL x) (Nat.add (Nat.mul (nat_lit 6) j) k))))))

@[expose] noncomputable def rowOK (MT W PL : Nat → Nat) (n i : Nat) : Bool :=
  strictB (MT i) (fun r => bAnd(Nat.blt r (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) n)),
    bIf(Nat.beq i (nat_lit 0), allN n (fun j => Nat.beq (b8 r j) j),
      strictB (MT (parK PL i)) (fun rp => strictB (labK PL i) (fun l =>
        allN n (fun j => Nat.beq (b8 r j) (lamK W l (b8 rp j))))))))

@[expose] noncomputable def ivOK (MT : Nat → Nat) (IV n i : Nat) : Bool :=
  strictB (b8 IV i) (fun v => bAnd(Nat.blt v n, bAnd(Nat.beq (tmK MT i v) (nat_lit 0),
    allN v (fun j => Bool.not (Nat.beq (tmK MT i j) (nat_lit 0))))))

@[expose] noncomputable def tinvK (IV i : Nat) : Nat := b8 IV i

@[expose] noncomputable def tcommK (MT : Nat → Nat) (IV x y : Nat) : Nat :=
  tmK MT (tmK MT (tmK MT x y) (tinvK IV x)) (tinvK IV y)

@[expose] noncomputable def commsK (MT : Nat → Nat) (IV n : Nat) (CM : Nat → Nat) :
    Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun _ cnt mask => Nat.add cnt (Nat.shiftLeft mask (nat_lit 16)))
    (fun _ ih q cnt mask => strictN (Nat.div q n) (fun a => strictN (Nat.mod q n) (fun b =>
      strictN (tcommK MT IV a b) (fun c => strictN (Nat.succ q) (fun q' =>
        nIf(Nat.beq cnt (nat_lit 65535), nat_lit 65535,
        nIf(hasBit mask c, ih q' cnt mask,
          nIf(Nat.beq (CM cnt) (Nat.lor c (Nat.lor (Nat.shiftLeft a (nat_lit 8))
              (Nat.shiftLeft b (nat_lit 16)))),
            strictN (Nat.succ cnt) (fun cnt' =>
              strictN (Nat.lor mask (Nat.shiftLeft (nat_lit 1) c)) (fun mask' => ih q' cnt' mask')),
            nat_lit 65535))))))))

@[expose] noncomputable def dtHead (MT CM DT : Nat → Nat) (nC nD h cur : Nat) : Nat :=
  foldUp nC (fun t cur => nIf(Nat.beq cur (nat_lit 0), nat_lit 0,
    strictN (tmK MT (b8 (CM t) 0) (b8 (DT h) 0)) (fun y =>
      nIf(anyN cur (fun i => Nat.beq (b8 (DT i) 0) y), cur,
        nIf(bAnd(Nat.blt cur nD, bAnd(Nat.beq (b8 (DT cur) 0) y, bAnd(Nat.beq (b8 (DT cur) 1) h,
            bAnd(Nat.beq (b8 (DT cur) 2) (b8 (CM t) 1), Nat.beq (b8 (DT cur) 3) (b8 (CM t) 2))))),
          Nat.succ cur, nat_lit 0))))) cur

@[expose] noncomputable def dtRun (MT CM DT : Nat → Nat) (nC nD : Nat) : Nat :=
  foldUp nD (fun h cur => nIf(Nat.blt h cur, dtHead MT CM DT nC nD h cur, cur)) (nat_lit 1)

@[expose] noncomputable def maskL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) x)) L

@[expose] noncomputable def lenL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ acc => Nat.succ acc) L

@[expose] noncomputable def incL (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih p => bAnd(Nat.ble p x, ih (Nat.succ x))) L (nat_lit 0)

@[expose] noncomputable def popN (M n : Nat) : Nat :=
  foldN n (fun i acc => nIf(hasBit M i, Nat.succ acc, acc)) (nat_lit 0)

@[expose] noncomputable def extK (MT : Nat → Nat) (n M x : Nat) : Bool :=
  bAnd(Bool.not (Nat.beq x (nat_lit 0)), bAnd(Nat.beq (tmK MT x x) (nat_lit 0),
  bAnd(Bool.not (hasBit M x),
    allN n (fun e => bIf(hasBit M e, Nat.beq (tmK MT x e) (tmK MT e x), true)))))

@[expose] noncomputable def spanM (MT : Nat → Nat) (n M x : Nat) : Nat :=
  foldN n (fun e acc => nIf(hasBit M e, Nat.lor acc (Nat.shiftLeft (nat_lit 1) (tmK MT x e)), acc)) M

@[expose] noncomputable def findM (NM : Nat → Nat) (cnt m : Nat) : Nat :=
  foldN cnt (fun i s => nIf(Nat.beq (NM i) m, i, s)) cnt

@[expose] noncomputable def eaOne (MT NM : Nat → Nat) (n nN M k cnt : Nat) : Nat :=
  foldUp n (fun x cnt => nIf(Nat.ble (nat_lit 1048576) cnt, cnt,
    nIf(extK MT n M x,
      strictN (spanM MT n M x) (fun s => nIf(Nat.beq (popN s n) (Nat.add k k),
        strictN (findM NM cnt s) (fun f => nIf(Nat.blt f cnt, cnt,
          nIf(bAnd(Nat.blt cnt nN, Nat.beq (NM cnt) s), Nat.succ cnt, nat_lit 1048576))),
        nat_lit 1048576)),
      cnt))) cnt

@[expose] noncomputable def listOfM (M n : Nat) (L : List Nat) : Bool :=
  bAnd(incL L, bAnd(Nat.beq (maskL L) M, CFSG.KS.Mathieu.allLtN n L))

@[expose] noncomputable def convRun (cs : List Char) : Nat → Nat → Nat → List Int →
    List (Nat × List Int) → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → List Int → List (Nat × List Int) → Bool)
    (fun ph _ _ _ CL => bAnd(Nat.beq ph (nat_lit 0), bAnd(Nat.beq ph (nat_lit 0),
      List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) CL)))
    (fun ch _ ih ph v len ws CL => strictB (Char.toNat ch) (fun c =>
      bIf(bAnd(Nat.ble (nat_lit 48) c, Nat.ble c (nat_lit 57)),
        bIf(Nat.beq ph (nat_lit 0),
          strictB (Nat.add (Nat.mul v (nat_lit 10)) (Nat.sub c (nat_lit 48))) (fun v' =>
            strictB (Nat.succ len) (fun len' => ih (nat_lit 0) v' len' ws CL)),
        bIf(bIf(Nat.beq ph (nat_lit 2), true, Nat.beq ph (nat_lit 5)),
          strictB (Nat.add (Nat.mul v (nat_lit 10)) (Nat.sub c (nat_lit 48))) (fun v' =>
            strictB (Nat.succ len) (fun len' => ih (nat_lit 2) v' len' ws CL)),
          false)),
      bIf(Nat.beq ph (nat_lit 0),
        bAnd(Nat.beq c (nat_lit 32), bAnd(Nat.blt (nat_lit 0) len,
          List.rec (motive := fun _ => Bool) false
            (fun e _ _ => Prod.rec (motive := fun _ => Bool) (fun k w =>
              bAnd(Nat.beq k v, ih (nat_lit 3) (nat_lit 0) (nat_lit 0) w CL)) e) CL)),
      bIf(Nat.beq ph (nat_lit 3), bAnd(Nat.beq c (nat_lit 58), ih (nat_lit 4) v len ws CL),
      bIf(Nat.beq ph (nat_lit 4), bAnd(Nat.beq c (nat_lit 32),
          ih (nat_lit 5) (nat_lit 0) (nat_lit 0) ws CL),
      bIf(Nat.beq ph (nat_lit 5), bAnd(Nat.beq c (nat_lit 10),
          bAnd(List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ws,
            List.rec (motive := fun _ => Bool) false
              (fun _ CL' _ => ih (nat_lit 0) (nat_lit 0) (nat_lit 0) [] CL') CL)),
      bAnd(Nat.beq ph (nat_lit 2), bAnd(Nat.blt (nat_lit 0) len,
        List.rec (motive := fun _ => Bool) false
          (fun z rest _ => bAnd(Nat.beq (CFSG.KS.Mathieu.icode z) (Nat.add v v),
            bIf(Nat.beq c (nat_lit 32), ih (nat_lit 2) (nat_lit 0) (nat_lit 0) rest CL,
              bAnd(Nat.beq c (nat_lit 10),
                bAnd(List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) rest,
                  List.rec (motive := fun _ => Bool) false
                    (fun _ CL' _ => ih (nat_lit 0) (nat_lit 0) (nat_lit 0) [] CL') CL)))))
          ws)))))))))
    cs

@[expose] noncomputable def convK (cs : List Char) (CL : List (Nat × List Int)) : Bool :=
  convRun cs (nat_lit 0) (nat_lit 0) (nat_lit 0) [] CL

@[expose] noncomputable def tpowK (MT : Nat → Nat) (i e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ acc => strictN acc (fun a => tmK MT a i)) e

@[expose] noncomputable def dMask (DT : Nat → Nat) (nD : Nat) : Nat :=
  foldN nD (fun k acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (b8 (DT k) 0))) (nat_lit 0)

@[expose] noncomputable def closedM (MT : Nat → Nat) (n M : Nat) : Bool :=
  allN n (fun a => bIf(hasBit M a, allN n (fun b => bIf(hasBit M b, hasBit M (tmK MT a b), true)),
    true))

@[expose] noncomputable def ord8K (MT : Nat → Nat) (i : Nat) : Bool :=
  strictB (tpowK MT i (nat_lit 4)) (fun p4 => strictB (tmK MT (tmK MT (tmK MT (tmK MT p4 i) i) i) i)
    (fun p8 => bAnd(bIf(Nat.beq p8 (nat_lit 0), true, Nat.beq p8 (nat_lit 6)),
      Bool.not (bIf(Nat.beq p4 (nat_lit 0), true, Nat.beq p4 (nat_lit 6))))))

@[expose] noncomputable def rowChk (MT : Nat → Nat) (IV n DM i : Nat) : Bool :=
  bAnd(ivOK MT IV n i,
  bAnd(Nat.beq (nIf(allN n (fun j => Nat.beq (tmK MT i j) (tmK MT j i)), nat_lit 1, nat_lit 0))
      (nIf(bIf(Nat.beq i (nat_lit 0), true, Nat.beq i (nat_lit 6)), nat_lit 1, nat_lit 0)),
  bAnd(allN n (fun b => hasBit DM (tcommK MT IV i b)),
  bAnd(hasBit DM (tmK MT i i),
    bIf(hasBit DM i, true, bIf(allN n (fun d => bIf(hasBit DM d, ord8K MT (tmK MT i d), true)),
      hasBit DM (tmK MT (tinvK IV 38) i), true))))))

@[expose] noncomputable def dChk (MT : Nat → Nat) (IV n : Nat) (DT : Nat → Nat) (nD : Nat) : Bool :=
  strictB (dMask DT nD) (fun DM =>
  bAnd(Nat.beq nD (nat_lit 32), bAnd(Nat.beq (b8 (DT 0) 0) (nat_lit 0),
  bAnd(Nat.beq (popN DM n) nD, bAnd(Nat.blt DM (Nat.shiftLeft (nat_lit 1) n),
  bAnd(closedM MT n DM, bAnd(hasBit DM (nat_lit 0), bAnd(hasBit DM (nat_lit 6),
  bAnd(allN nD (fun k => bAnd(Nat.blt (b8 (DT k) 0) n, hasBit DM (tinvK IV (b8 (DT k) 0)))),
  bAnd(allN nD (fun k => bIf(Nat.beq k (nat_lit 0), true,
    bAnd(Nat.blt (b8 (DT k) 1) k, bAnd(Nat.blt (b8 (DT k) 2) n, bAnd(Nat.blt (b8 (DT k) 3) n,
      Nat.beq (tmK MT (tcommK MT IV (b8 (DT k) 2) (b8 (DT k) 3)) (b8 (DT (b8 (DT k) 1)) 0))
        (b8 (DT k) 0)))))),
  bAnd(Nat.blt (nat_lit 38) n, bAnd(Bool.not (hasBit DM (nat_lit 38)),
    allN nD (fun k => ord8K MT (tmK MT 38 (b8 (DT k) 0)))))))))))))))

@[expose] noncomputable def eChk (MT : Nat → Nat) (n : Nat) (L : List Nat) : Bool :=
  strictB (maskL L) (fun M => bAnd(Nat.beq (lenL L) (nat_lit 16), bAnd(Nat.beq (popN M n) (nat_lit 16),
  bAnd(CFSG.KS.Mathieu.allLtN n L, bAnd(closedM MT n M, bAnd(hasBit M (nat_lit 0),
  bAnd(allN n (fun x => bIf(hasBit M x, bIf(Nat.beq x (nat_lit 0), true,
      Nat.beq (tmK MT x x) (nat_lit 0)), true)),
  bAnd(allN n (fun a => bIf(hasBit M a, allN n (fun b => bIf(hasBit M b,
      Nat.beq (tmK MT a b) (tmK MT b a), true)), true)),
    allN n (fun x => Bool.not (extK MT n M x))))))))))

@[expose] noncomputable def qChk (MT : Nat → Nat) (IV n : Nat) (Q E0 E1 : List Nat) (f : Nat) : Bool :=
  strictB (maskL Q) (fun QM => strictB (maskL E0) (fun M0 => strictB (maskL E1) (fun M1 =>
  bAnd(Nat.beq (lenL Q) (nat_lit 64), bAnd(Nat.beq (popN QM n) (nat_lit 64),
  bAnd(CFSG.KS.Mathieu.allLtN n Q, bAnd(closedM MT n QM, bAnd(hasBit QM (nat_lit 0),
  bAnd(allN n (fun q => bIf(hasBit QM q, bAnd(hasBit QM (tinvK IV q),
    bAnd(anyN n (fun a => bIf(hasBit M0 a, anyN n (fun b => bIf(hasBit M1 b,
        Nat.beq (tmK MT a b) q, false)), false)),
      Nat.beq (nIf(allN n (fun r => bIf(hasBit QM r, Nat.beq (tmK MT q r) (tmK MT r q), true)),
        nat_lit 1, nat_lit 0))
        (nIf(bIf(Nat.beq q 0, true, bIf(Nat.beq q 6, true, bIf(Nat.beq q 113, true,
          Nat.beq q 207))), nat_lit 1, nat_lit 0)))), true)),
  bAnd(Nat.beq (Nat.land M0 QM) M0, bAnd(Nat.beq (Nat.land M1 QM) M1,
  bAnd(allN n (fun q => bIf(bIf(Nat.beq q 0, true, bIf(Nat.beq q 6, true, bIf(Nat.beq q 113, true,
      Nat.beq q 207))), bAnd(hasBit QM q, Nat.beq (tmK MT q q) (nat_lit 0)), true)),
    hasBit QM f))))))))))))

end CFSG.KS.SporSch.LySyl

end
