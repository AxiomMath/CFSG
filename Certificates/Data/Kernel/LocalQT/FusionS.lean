module

public import Certificates.Data.Kernel.LocalQT.BaseS
public import Certificates.Data.Kernel.LocalQT.FusionB

public section

namespace CFSG.KC.LQT.FS

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.BS CFSG.KC.LQT.RW CFSG.KC.LQT.RB
open CFSG.KC.LQT.FB

@[expose] noncomputable def discT (W g : Nat) (CT : Nat → Nat) (p i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => g)
    (fun _ ih t => Bool.rec (motive := fun _ => Nat) (ih (Nat.succ t)) t
      (Nat.beq (fieldT W CT (Nat.add (Nat.mul p (Nat.add g g)) t)) i)) g 0

@[expose] noncomputable def discK (W g : Nat) (PT CT : Nat → Nat) (i : Nat) : Nat :=
  (fun (p : Nat) => Nat.add (Nat.mul p g) (discT W g CT p i)) (fieldT W PT i)

@[expose] noncomputable def bfsI (w nb r M lg W g : Nat) (app : Nat → List Nat → List Nat)
    (E BO IB : Nat → Nat) (PT CT : Nat → Nat) (oC i : Nat) : Bool :=
  (fun (T : List Nat) => allBs [Nat.blt (BO i) M, Nat.beq (IB (BO i)) i,
    impB (Nat.beq i 0) (Nat.beq (E (BO i)) oC),
    allL (rangeK g) (fun t => (fun (c : Nat) => (fun (j : Nat) =>
        (fun (k : Nat) => allBs [Nat.beq (E j) c, Nat.beq (IB j) k, Nat.blt k M,
          orB (Nat.beq k 0) (Nat.ble (discK W g PT CT k) (Nat.add (Nat.mul i g) t))])
        (fieldT W CT (Nat.add (Nat.mul i (Nat.add g g)) t)))
      (findS w nb M lg E (keyC w nb c)))
      (codeK w (app t T))),
    orB (Nat.beq i 0) ((fun (p : Nat) => allBs [Nat.blt p i,
        Nat.blt (discT W g CT p i) g,
        impB (Nat.blt (Nat.succ i) M) (Nat.blt (discK W g PT CT i) (discK W g PT CT (Nat.succ i)))])
      (fieldT W PT i))])
  (decW w r (E (BO i)))

@[expose] noncomputable def bfsS (w : Nat) (B : List Nat) (qp : List (Nat × Nat)) (TF : Nat → Nat)
    (RS : Nat) (RT : Nat → Nat) (M lg W : Nat) (E BO IB PT CT : Nat → Nat) (lo len : Nat) : Bool :=
  (fun (o : List Nat) => (fun (oC : Nat) =>
      allR lo len fun i => impB (Nat.blt i M)
        (bfsI w (lenA B) (lenA o) M lg W (lenA qp) (imgsR w RS RT) E BO IB PT CT oC i))
    (codeK w o))
  (ptsW w B (fstT TF qp))

@[expose] noncomputable def fusSH (n w W : Nat) (qp : List (Nat × Nat)) (TF : Nat → Nat)
    (M zi : Nat) (PT CT : Nat → Nat) (ZT : Nat) (wits : List (List Nat × List Nat × Nat))
    (gws : List (List Nat)) : Bool :=
  (fun (g : Nat) => (fun (mul : Nat → Nat → Nat) => allBs [
      Nat.blt zi M, notB (Nat.beq zi 0), Nat.beq (mul zi zi) 0,
      allL (rangeK g) (fun j => Nat.beq (mul (fieldT W CT j) zi) (mul zi (fieldT W CT j))),
      Nat.beq ZT (idxW n w W g PT CT (fstT TF qp) M zi),
      allL (witIdx wits) (fun c => Nat.blt c M),
      allL (rangeK g) (fun j =>
        Nat.beq (evalIdxW mul (witIdx wits) (getLL gws j)) (fieldT W CT j))])
    (mulT W g M PT CT))
  (lenA qp)

@[expose] noncomputable def fusC (W g M zi : Nat) (PT CT : Nat → Nat) (lo len : Nat) : Bool :=
  (fun (mul : Nat → Nat → Nat) => allR lo len fun i => impB (Nat.blt i M)
      (orB (notB (allL (rangeK g) fun j => Nat.beq (mul (fieldT W CT j) i) (mul i (fieldT W CT j))))
        (orB (Nat.beq i 0) (Nat.beq i zi))))
    (mulT W g M PT CT)

@[expose] noncomputable def witE (E BO : Nat → Nat) (wits : List (List Nat × List Nat × Nat))
    (j : Nat) : Nat :=
  E (BO (getK (witIdx wits) j))

end CFSG.KC.LQT.FS

end
