module

public import Certificates.Data.Kernel.LocalQT.BaseT
public import Certificates.Data.Kernel.LocalQT.RankB

public section

namespace CFSG.KC.LQT.FB

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.RW CFSG.KC.LQT.RB

@[expose] noncomputable def getLL (L : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih j => Nat.rec (motive := fun _ => List Nat) x (fun j' _ => ih j') j) L i

@[expose] noncomputable def getW (L : List (List Nat × List Nat × Nat)) (i : Nat) :
    List Nat × List Nat × Nat :=
  List.rec (motive := fun _ => Nat → List Nat × List Nat × Nat) (fun _ => ([], [], 0))
    (fun x _ ih j => Nat.rec (motive := fun _ => List Nat × List Nat × Nat) x (fun j' _ => ih j') j)
    L i

@[expose] noncomputable def wordsOf (wits : List (List Nat × List Nat × Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) []
    (fun wt _ ih => List.cons wt.1 (List.cons wt.2.1 ih)) wits

@[expose] noncomputable def segW (n w a b : Nat) (seg : List Nat) (acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun x _ ih acc => CFSG.KC.LQT.Syl.letN
      (mulW n w acc (Bool.rec (motive := fun _ => Nat) b a (Nat.beq x 0))) ih) seg acc

@[expose] noncomputable def wordCk (n w a b : Nat) (ws : List (List Nat)) (s R : Nat) (CP : Nat → Nat)
    (q : Nat) : Bool :=
  (fun (u c : Nat) => andB (impB (Nat.beq c 0) (Nat.beq (CP (Nat.mul u R)) (oneW n w)))
      (impB (Nat.blt (Nat.succ c) R)
        (Nat.beq (CP (Nat.succ q)) (segW n w a b (sliceK (getLL ws u) (Nat.mul c s) s) (CP q)))))
    (Nat.div q R) (Nat.mod q R)

@[expose] noncomputable def idxW (n w W g : Nat) (PT CT : Nat → Nat) (G : List Nat) (f : Nat) :
    Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => oneW n w)
    (fun _ ih i => Bool.rec (motive := fun _ => Nat)
      (CFSG.KC.LQT.Syl.letN (ih (fieldT W PT i)) fun t =>
        mulW n w (genW n w G (genIdxT W g (Nat.add g g) PT CT i)) t)
      (oneW n w) (Nat.beq i 0)) f

@[expose] noncomputable def evalIdxW (mul : Nat → Nat → Nat) (cs wd : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun p _ ih => mul (getK cs p) ih) wd

@[expose] noncomputable def witIdx (wits : List (List Nat × List Nat × Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun wt _ ih => List.cons wt.2.2 ih) wits

@[expose] noncomputable def fusQ (w W g N : Nat) (CT : Nat → Nat) (zi : Nat)
    (mul : Nat → Nat → Nat) (Ts : List (List Nat)) (TS : Nat → Nat)
    (wits : List (List Nat × List Nat × Nat)) (gws : List (List Nat)) : Bool :=
  allBs [Nat.blt zi N, notB (Nat.beq zi 0), Nat.beq (mul zi zi) 0,
    allL (rangeK g) (fun j => Nat.beq (mul (fieldT W CT j) zi) (mul zi (fieldT W CT j))),
    allR 0 N (fun i => orB (notB (allL (rangeK g) fun j =>
        Nat.beq (mul (fieldT W CT j) i) (mul i (fieldT W CT j))))
      (orB (Nat.beq i 0) (Nat.beq i zi))),
    allR 0 (lenA wits) (fun j => (fun (c : Nat) => andB (Nat.blt c N)
      (Nat.beq (codeK w (getLL Ts c)) (TS j))) (getK (witIdx wits) j)),
    allL (rangeK g) (fun j =>
      Nat.beq (evalIdxW mul (witIdx wits) (getLL gws j)) (fieldT W CT j))]

@[expose] noncomputable def fusBE (n w W g k fuel zi PK CK RP RC : Nat) (PT CT : Nat → Nat)
    (ZT : Nat) (G : List Nat) (TS : Nat → Nat) (wits : List (List Nat × List Nat × Nat))
    (gws : List (List Nat)) (E : ES × Nat × List (List Nat)) : Bool :=
  allBs [enumOK k fuel E,
    allL E.1.par (fun x => Nat.blt x (Nat.shiftLeft 1 W)),
    allL E.1.cl (fun x => Nat.blt x (Nat.shiftLeft 1 W)),
    Nat.beq PK (codeK W (revOn E.1.par [])), Nat.beq CK (codeK W (revOn E.1.cl [])),
    rowsOK W E.1.cnt RP PK PT, rowsOK W (Nat.mul E.1.cnt (Nat.add g g)) RC CK CT,
    Nat.beq ZT (idxW n w W g PT CT G E.1.cnt zi),
    fusQ w W g E.1.cnt CT zi (mulT W g E.1.cnt PT CT) (revOn E.1.rev []) TS wits gws]

@[expose] noncomputable def fusBH (n w W : Nat) (B ta tb : List Nat) (prog qp : List (Nat × Nat))
    (TF : Nat → Nat) (K m RS : Nat) (RT : Nat → Nat) (k fuel dd zi PK CK RP RC : Nat)
    (PT CT : Nat → Nat) (ZT : Nat) (TS : Nat → Nat) (wits : List (List Nat × List Nat × Nat))
    (gws : List (List Nat)) : Bool :=
  (fun (N : Nat) => (fun (G : List Nat) => allBs [tabL n ta, tabL n tb, slpOKK prog 2,
    Nat.beq (TF 0) (codeK w ta), Nat.beq (TF 1) (codeK w tb),
    Nat.ble N (Nat.mul K m), Nat.ble n (Nat.mul 64 RS),
    allA qp (fun p => andB (Nat.blt p.1 N) (Nat.blt p.2 N)),
    allA qp (fun p => Nat.beq (mulW n w (TF p.2) (TF p.1)) (oneW n w)),
    allL B (fun b => Nat.blt b n),
    rowsT w RS RT G,
    fusBE n w W (lenA qp) k fuel zi PK CK RP RC PT CT ZT G TS wits gws
      (enumW w (lenA B) (lenA qp) (imgsR w RS RT) (rangeK (lenA qp)) (ptsW w B G) dd)])
    (fstT TF qp))
  (Nat.add (lenA prog) 2)

@[expose] noncomputable def fusBW (n w : Nat) (B : List Nat) (qp : List (Nat × Nat))
    (TF : Nat → Nat) (ZT : Nat) (TS : Nat → Nat) (wits : List (List Nat × List Nat × Nat))
    (s R : Nat) (CP : Nat → Nat) (j : Nat) : Bool :=
  (fun (wt : List Nat × List Nat × Nat) (x y : Nat) => allBs [
      Nat.ble (lenA wt.1) (Nat.mul (Nat.sub R 1) s), Nat.ble (lenA wt.2.1) (Nat.mul (Nat.sub R 1) s),
      Nat.beq (mulW n w y x) (oneW n w),
      Nat.beq (codeK w (List.rec (motive := fun _ => List Nat) []
          (fun p _ ih => List.cons (cjW w ZT x y p) ih) (ptsW w B (fstT TF qp))))
        (TS j)])
  (getW wits j) (CP (Nat.add (Nat.mul (Nat.add j j) R) (Nat.sub R 1)))
    (CP (Nat.add (Nat.mul (Nat.succ (Nat.add j j)) R) (Nat.sub R 1)))

end CFSG.KC.LQT.FB

end
