module

public import Certificates.Data.Kernel.LocalQT.BaseW

public section

namespace CFSG.KC.LQT.BT

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW

@[expose] noncomputable def nodesT (n w : Nat) (prog : List (Nat × Nat)) (TF : Nat → Nat)
    (lo len : Nat) : Bool :=
  allR lo len fun j => impB (andB (Nat.ble 2 j) (Nat.blt j (Nat.add (lenA prog) 2)))
    ((fun p => Nat.beq (TF j) (mulW n w (TF p.1) (TF p.2))) (nthP prog (Nat.sub j 2)))

@[expose] noncomputable def rowW (w x k : Nat) : Nat :=
  Nat.land (Nat.shiftRight x (Nat.mul (Nat.mul 64 w) k))
    (Nat.sub (Nat.shiftLeft 1 (Nat.mul 64 w)) 1)

@[expose] noncomputable def imgR (w RS : Nat) (RT : Nat → Nat) (t p : Nat) : Nat :=
  Nat.land (Nat.shiftRight (RT (Nat.add (Nat.mul t RS) (Nat.shiftRight p 6)))
    (Nat.mul w (Nat.land p 63))) (Nat.sub (Nat.shiftLeft 1 w) 1)

@[expose] noncomputable def imgsR (w RS : Nat) (RT : Nat → Nat) (t : Nat) (l : List Nat) :
    List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun x _ ih => letLs (imgR w RS RT t x) fun y => List.cons y ih) l

@[expose] noncomputable def rowsT (w RS : Nat) (RT : Nat → Nat) (G : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun g _ ih t => andB (allR 0 RS fun k => Nat.beq (RT (Nat.add (Nat.mul t RS) k)) (rowW w g k))
      (ih (Nat.succ t))) G 0

@[expose] noncomputable def rangeK (m : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih i => List.cons i (ih (Nat.succ i))) m 0

@[expose] noncomputable def fstT (TF : Nat → Nat) (qp : List (Nat × Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun p _ ih => List.cons (TF p.1) ih) qp

@[expose] noncomputable def baseTK (n w : Nat) (B ta tb : List Nat) (prog qp : List (Nat × Nat))
    (TF : Nat → Nat) (K m RS : Nat) (RT : Nat → Nat) (zn gn gin hn hin k fuel dd : Nat) : Bool :=
  (fun (N : Nat) => allBs [tabL n ta, tabL n tb, slpOKK prog 2,
    Nat.beq (TF 0) (codeK w ta), Nat.beq (TF 1) (codeK w tb),
    Nat.ble N (Nat.mul K m), Nat.ble n (Nat.mul 64 RS),
    allA qp (fun p => andB (Nat.blt p.1 N) (Nat.blt p.2 N)),
    allBs [Nat.blt zn N, Nat.blt gn N, Nat.blt gin N, Nat.blt hn N, Nat.blt hin N],
    allA qp (fun p => Nat.beq (mulW n w (TF p.2) (TF p.1)) (oneW n w)),
    Nat.beq (mulW n w (TF gin) (TF gn)) (oneW n w), Nat.beq (mulW n w (TF hin) (TF hn)) (oneW n w),
    allL B (fun b => Nat.blt b n),
    rowsT w RS RT (fstT TF qp),
    baseWQ w B (imgsR w RS RT) (rangeK (lenA qp)) (lenA qp) (ptsW w B (fstT TF qp)) (TF zn) (TF gn)
      (TF gin) (TF hn) (TF hin) k fuel dd])
  (Nat.add (lenA prog) 2)

end CFSG.KC.LQT.BT

end
