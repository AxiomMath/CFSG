module

public import Certificates.Data.Kernel.LocalQT.RankF
public import Certificates.Data.Kernel.LocalQT.BaseT

public section

namespace CFSG.KC.LQT.RB

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.RW CFSG.KC.LQT.RF

@[expose] noncomputable def fieldT (W : Nat) (T : Nat → Nat) (x : Nat) : Nat :=
  imgW W (T (Nat.shiftRight x 6)) (Nat.land x 63)

@[expose] noncomputable def genIdxT (W g gg : Nat) (PT CT : Nat → Nat) (i : Nat) : Nat :=
  findW g fun j => Nat.beq (fieldT W CT (Nat.add (Nat.mul (fieldT W PT i) gg) j)) i

@[expose] noncomputable def mulT (W g N : Nat) (PT CT : Nat → Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ k => k)
    (fun _ ih i k => Bool.rec (motive := fun _ => Nat)
      (fieldT W CT (Nat.add (Nat.mul (ih (fieldT W PT i) k) (Nat.add g g))
        (genIdxT W g (Nat.add g g) PT CT i))) k
      (Nat.beq i 0)) N

@[expose] noncomputable def invsB (N : Nat) (mul : Nat → Nat → Nat) : List Nat :=
  filterN N fun i => andB (notB (Nat.beq i 0)) (Nat.beq (mul i i) 0)

@[expose] noncomputable def rowsOK (W N R x : Nat) (T : Nat → Nat) : Bool :=
  andB (Nat.ble N (Nat.mul 64 R)) (allR 0 R fun r => Nat.beq (T r) (rowW W x r))

@[expose] noncomputable def rankBE (W g k fuel zi K L PK CK RP RC : Nat) (PT CT : Nat → Nat)
    (E : ES × Nat × List (List Nat)) : Bool :=
  (fun (mul : Nat → Nat → Nat) => allBs [enumOK k fuel E,
    allL E.1.par (fun x => Nat.blt x (Nat.shiftLeft 1 W)),
    allL E.1.cl (fun x => Nat.blt x (Nat.shiftLeft 1 W)),
    Nat.beq PK (codeK W (revOn E.1.par [])), Nat.beq CK (codeK W (revOn E.1.cl [])),
    rowsOK W E.1.cnt RP PK PT, rowsOK W (Nat.mul E.1.cnt (Nat.add g g)) RC CK CT,
    Nat.blt zi E.1.cnt, notB (Nat.beq zi 0), Nat.beq (mul zi zi) 0,
    allR 0 E.1.cnt (fun i => Nat.beq (mul zi i) (mul i zi)),
    Nat.ble (lenA (invsB E.1.cnt mul)) (Nat.mul K L)])
  (mulT W g E.1.cnt PT CT)

@[expose] noncomputable def rankBH (n w W : Nat) (B ta tb : List Nat) (prog qp : List (Nat × Nat))
    (k fuel dd zi K L PK CK RP RC : Nat) (PT CT : Nat → Nat) : Bool :=
  andB (tabL n ta) (andB (tabL n tb) (andB (slpOKK prog 2)
    ((fun (R : List Nat) => andB (qpW n w B R qp)
      ((fun (G : List Nat) => rankBE W (lenA qp) k fuel zi K L PK CK RP RC PT CT
          (enumW w (lenA B) (lenA qp) (imgsW w) G (ptsW w B G) dd))
        (fstN R qp)))
    (slpW n w (codeK w ta) (codeK w tb) prog))))

@[expose] noncomputable def rankBP (W g N : Nat) (PT CT : Nat → Nat) (d zi lo len : Nat) : Bool :=
  (fun (mul : Nat → Nat → Nat) =>
      (fun (invs : List Nat) => allL (sliceK invs lo len) (branchF mul invs zi d)) (invsB N mul))
    (mulT W g N PT CT)

end CFSG.KC.LQT.RB

end
