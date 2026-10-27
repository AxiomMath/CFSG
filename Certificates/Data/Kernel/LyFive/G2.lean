module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.SporSch.LySeven

public section

namespace CFSG.KC.LyG2

open CFSG.KC.Enum CFSG.KS.SporSch.LySev

@[expose] noncomputable def ln (v i : Nat) : Nat := fld(v, Nat.mul (nat_lit 20) i, nat_lit 1048575)

@[expose] noncomputable def QM7 : Nat := nat_lit 338953462176364882166965176520833761535

@[expose] noncomputable def getL (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih i => Nat.rec (motive := fun _ => Nat) a (fun k _ => ih k) i) l i

@[expose] noncomputable def getLL (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun a _ ih i => Nat.rec (motive := fun _ => List Nat) a (fun k _ => ih k) i) l i

@[expose] noncomputable def snoc (l : List Nat) (x : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [x] (fun a _ ih => a :: ih) l

@[expose] noncomputable def colSum (v : Nat) (cs : List Nat) (j : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun c _ ih j => Nat.add (Nat.mul (ln v j) c) (ih (Nat.succ j))) cs j

@[expose] noncomputable def mvL (cols : List Nat) (v : Nat) : Nat :=
  red5 QM7 (colSum v cols (nat_lit 0))

@[expose] noncomputable def crsSum (CC : List (List Nat)) (u v : Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun row _ ih i => Nat.add (Nat.mul (ln u i) (mvL row v)) (ih (Nat.succ i))) CC i

@[expose] noncomputable def crs (CC : List (List Nat)) (u v : Nat) : Nat :=
  red5 QM7 (crsSum CC u v (nat_lit 0))

@[expose] noncomputable def bt (TT : List Nat) (u v : Nat) : Nat :=
  Nat.mod (colSum (mvL TT v) [ln u (nat_lit 0), ln u (nat_lit 1), ln u (nat_lit 2),
    ln u (nat_lit 3), ln u (nat_lit 4), ln u (nat_lit 5), ln u (nat_lit 6)] (nat_lit 0))
    (nat_lit 5)

@[expose] noncomputable def linSum (cs us : List Nat) : Nat :=
  List.rec (motive := fun _ => List Nat → Nat) (fun _ => nat_lit 0)
    (fun c _ ih us => List.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun u us' _ => Nat.add (Nat.mul c u) (ih us')) us) cs us

@[expose] noncomputable def lin (cs us : List Nat) : Nat := red5 QM7 (linSum cs us)

@[expose] noncomputable def stepI (CC : List (List Nat)) (TT : List Nat) (ops : List (List Nat))
    (gv : List Nat) (ins : Nat × Nat × Nat × List Nat) (ih : List Nat → Bool) (us : List Nat) :
    Bool :=
  bIf(Nat.beq ins.1 (nat_lit 0), strictB (getL gv ins.2.1) (fun v => ih (snoc us v)),
  bIf(Nat.beq ins.1 (nat_lit 1),
    strictB (mvL (getLL ops ins.2.1) (getL us ins.2.2.1)) (fun v => ih (snoc us v)),
  bIf(Nat.beq ins.1 (nat_lit 2),
    strictB (crs CC (getL us ins.2.1) (getL us ins.2.2.1)) (fun v => ih (snoc us v)),
  bIf(Nat.beq ins.1 (nat_lit 3),
    bAnd(Nat.beq (mvL (getLL ops ins.2.1) (getL us ins.2.2.1)) (lin ins.2.2.2 us), ih us),
  bIf(Nat.beq ins.1 (nat_lit 4),
    bAnd(Nat.beq (crs CC (getL us ins.2.1) (getL us ins.2.2.1)) (lin ins.2.2.2 us), ih us),
  bIf(Nat.beq ins.1 (nat_lit 5),
    bAnd(Nat.beq (bt TT (getL us ins.2.1) (getL us ins.2.2.1)) (getL ins.2.2.2 (nat_lit 0)),
      ih us),
  bIf(Nat.beq ins.1 (nat_lit 6),
    bAnd(Bool.not (Nat.beq (getL us ins.2.1) (nat_lit 0)), ih us), false)))))))

@[expose] noncomputable def runI (CC : List (List Nat)) (TT : List Nat) (ops : List (List Nat))
    (gv : List Nat) (ins : List (Nat × Nat × Nat × List Nat)) (us : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun i _ ih us => stepI CC TT ops gv i ih us) ins us

@[expose] noncomputable def stkI (CC : List (List Nat)) (ops : List (List Nat)) (gv : List Nat)
    (ins : List (Nat × Nat × Nat × List Nat)) (us : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun us => us)
    (fun i _ ih us =>
      Bool.rec (motive := fun _ => List Nat)
        (Bool.rec (motive := fun _ => List Nat)
          (Bool.rec (motive := fun _ => List Nat) (ih us)
            (ih (snoc us (crs CC (getL us i.2.1) (getL us i.2.2.1)))) (Nat.beq i.1 (nat_lit 2)))
          (ih (snoc us (mvL (getLL ops i.2.1) (getL us i.2.2.1)))) (Nat.beq i.1 (nat_lit 1)))
        (ih (snoc us (getL gv i.2.1))) (Nat.beq i.1 (nat_lit 0))) ins us

@[expose] noncomputable def invChk (cols ui : List Nat) : Bool :=
  bAnd(Nat.beq (mvL cols (getL ui 0)) (nat_lit 1),
  bAnd(Nat.beq (mvL cols (getL ui 1)) (nat_lit 1048576),
  bAnd(Nat.beq (mvL cols (getL ui 2)) (nat_lit 1099511627776),
  bAnd(Nat.beq (mvL cols (getL ui 3)) (nat_lit 1152921504606846976),
  bAnd(Nat.beq (mvL cols (getL ui 4)) (nat_lit 1208925819614629174706176),
  bAnd(Nat.beq (mvL cols (getL ui 5)) (nat_lit 1267650600228229401496703205376),
    Nat.beq (mvL cols (getL ui 6)) (nat_lit 1329227995784915872903807060280344576)))))))

@[expose] noncomputable def autChk (CC : List (List Nat)) (g : List Nat) : Bool :=
  allN (nat_lit 49) (fun t => Nat.beq
    (mvL g (getL (getLL CC (Nat.div t (nat_lit 7))) (Nat.mod t (nat_lit 7))))
    (crs CC (getL g (Nat.div t (nat_lit 7))) (getL g (Nat.mod t (nat_lit 7)))))

@[expose] noncomputable def redL (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun v _ ih => bAnd(Nat.blt v
    (nat_lit 1393796574908163946345982392040522594123776),
    bAnd(Nat.blt (ln v (nat_lit 0)) (nat_lit 5), bAnd(Nat.blt (ln v (nat_lit 1)) (nat_lit 5),
    bAnd(Nat.blt (ln v (nat_lit 2)) (nat_lit 5), bAnd(Nat.blt (ln v (nat_lit 3)) (nat_lit 5),
    bAnd(Nat.blt (ln v (nat_lit 4)) (nat_lit 5), bAnd(Nat.blt (ln v (nat_lit 5)) (nat_lit 5),
    bAnd(Nat.blt (ln v (nat_lit 6)) (nat_lit 5), ih))))))))) l

@[expose] noncomputable def lenL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def lt5L (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ ih => bAnd(Nat.blt c (nat_lit 5), ih)) l

@[expose] noncomputable def insOK (ins : List (Nat × Nat × Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun i _ ih => bAnd(Nat.ble (lenL i.2.2.2) (nat_lit 63), bAnd(lt5L i.2.2.2, ih))) ins

@[expose] noncomputable def matOK (cols : List Nat) : Bool :=
  bAnd(Nat.ble (lenL cols) (nat_lit 7), redL cols)

@[expose] noncomputable def lenLL (l : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def matsOK (l : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun m _ ih => bAnd(matOK m, ih)) l

@[expose] noncomputable def trK (CC : List (List Nat)) (i j : Nat) : Nat :=
  Nat.add (ln (crs CC (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 20) i))
    (getL (getLL CC j) (nat_lit 0))) (nat_lit 0)) (Nat.add
    (ln (crs CC (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 20) i)) (getL (getLL CC j) (nat_lit 1))) (nat_lit 1))
    (Nat.add
    (ln (crs CC (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 20) i)) (getL (getLL CC j) (nat_lit 2))) (nat_lit 2))
    (Nat.add
    (ln (crs CC (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 20) i)) (getL (getLL CC j) (nat_lit 3))) (nat_lit 3))
    (Nat.add
    (ln (crs CC (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 20) i)) (getL (getLL CC j) (nat_lit 4))) (nat_lit 4))
    (Nat.add
    (ln (crs CC (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 20) i)) (getL (getLL CC j) (nat_lit 5))) (nat_lit 5))
    (ln (crs CC (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 20) i)) (getL (getLL CC j) (nat_lit 6))) (nat_lit 6)))))))

@[expose] noncomputable def tChk (CC : List (List Nat)) (TT : List Nat) : Bool :=
  allN (nat_lit 49) (fun t => Nat.beq (ln (getL TT (Nat.mod t (nat_lit 7))) (Nat.div t (nat_lit 7)))
    (Nat.mod (trK CC (Nat.div t (nat_lit 7)) (Nat.mod t (nat_lit 7))) (nat_lit 5)))

@[expose] noncomputable def dataChk (CC : List (List Nat)) (TT : List Nat) : Bool :=
  bAnd(Nat.ble (lenLL CC) (nat_lit 7), bAnd(matsOK CC, bAnd(matOK TT, tChk CC TT)))

@[expose] noncomputable def dropL {α : Type} (n : Nat) (l : List α) : List α :=
  Nat.rec (motive := fun _ => List α → List α) (fun l => l)
    (fun _ ih l => ih (List.rec (motive := fun _ => List α) [] (fun _ t _ => t) l)) n l

@[expose] noncomputable def takeL {α : Type} (n : Nat) (l : List α) : List α :=
  List.rec (motive := fun _ => Nat → List α) (fun _ => [])
    (fun a _ ih n => Nat.rec (motive := fun _ => List α) [] (fun k _ => a :: ih k) n) l n

@[expose] noncomputable def allL {α : Type} (l : List α) (p : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(p a, ih)) l

@[expose] noncomputable def commChk (R g : List Nat) : Bool :=
  allN (nat_lit 7) (fun t => Nat.beq (mvL g (getL R t)) (mvL R (getL g t)))

@[expose] noncomputable def witOK (CC : List (List Nat)) (R : List Nat) (w : List Nat × List Nat) : Bool :=
  bAnd(Nat.beq (lenL w.1) (nat_lit 7), bAnd(matOK w.1, bAnd(matOK w.2, bAnd(invChk w.1 w.2,
    bAnd(autChk CC w.1, commChk R w.1)))))

@[expose] noncomputable def lenA {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def keysInc (b : Nat) (l : List (List Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih prev => strictB (mvL w.1 b) (fun k => bAnd(Nat.blt prev k, ih k))) l (nat_lit 0)

@[expose] noncomputable def witBlk (CC : List (List Nat)) (R : List Nat) (l : List (List Nat × List Nat))
    (k : Nat) : Bool :=
  allL (takeL (nat_lit 150) (dropL (Nat.mul (nat_lit 150) k) l)) (witOK CC R)

@[expose] noncomputable def dec (n : Nat) : Nat :=
  Nat.add (Nat.mod n (nat_lit 5)) (Nat.add
    (Nat.shiftLeft (Nat.mod (Nat.div n (nat_lit 5)) (nat_lit 5)) (nat_lit 20)) (Nat.add
    (Nat.shiftLeft (Nat.mod (Nat.div n (nat_lit 25)) (nat_lit 5)) (nat_lit 40)) (Nat.add
    (Nat.shiftLeft (Nat.mod (Nat.div n (nat_lit 125)) (nat_lit 5)) (nat_lit 60)) (Nat.add
    (Nat.shiftLeft (Nat.mod (Nat.div n (nat_lit 625)) (nat_lit 5)) (nat_lit 80)) (Nat.add
    (Nat.shiftLeft (Nat.mod (Nat.div n (nat_lit 3125)) (nat_lit 5)) (nat_lit 100))
    (Nat.shiftLeft (Nat.mod (Nat.div n (nat_lit 15625)) (nat_lit 5)) (nat_lit 120)))))))

@[expose] noncomputable def passW (CC : List (List Nat)) (TT : List Nat) (ops : List (List Nat))
    (fixed : List Nat) (ins : List (Nat × Nat × Nat × List Nat)) (w : Nat) : Bool :=
  runI CC TT ops (snoc fixed w) ins []

@[expose] noncomputable def cntBlk (CC : List (List Nat)) (TT : List Nat) (ops : List (List Nat))
    (fixed : List Nat) (ins : List (Nat × Nat × Nat × List Nat)) (k : Nat) : Nat :=
  foldN (nat_lit 3125) (fun i acc => Nat.add acc
    (nIf(passW CC TT ops fixed ins (dec (Nat.add (Nat.mul (nat_lit 3125) k) i)), nat_lit 1,
      nat_lit 0)))
    (nat_lit 0)

@[expose] noncomputable def packCol (R : List Nat) (j : Nat) : Nat :=
  Nat.add (getL R j) (Nat.add (Nat.shiftLeft (getL R (Nat.add (nat_lit 7) j)) (nat_lit 20)) (Nat.add
    (Nat.shiftLeft (getL R (Nat.add (nat_lit 14) j)) (nat_lit 40)) (Nat.add
    (Nat.shiftLeft (getL R (Nat.add (nat_lit 21) j)) (nat_lit 60)) (Nat.add
    (Nat.shiftLeft (getL R (Nat.add (nat_lit 28) j)) (nat_lit 80)) (Nat.add
    (Nat.shiftLeft (getL R (Nat.add (nat_lit 35) j)) (nat_lit 100))
    (Nat.shiftLeft (getL R (Nat.add (nat_lit 42) j)) (nat_lit 120)))))))

@[expose] noncomputable def packCols (R : List Nat) : List Nat :=
  [packCol R 0, packCol R 1, packCol R 2, packCol R 3, packCol R 4, packCol R 5, packCol R 6]

@[expose] noncomputable def cntChk (CC : List (List Nat)) (TT : List Nat) (ops : List (List Nat))
    (fixed : List Nat) (ins : List (Nat × Nat × Nat × List Nat)) (cnt : List Nat) (k : Nat) : Bool :=
  Nat.beq (cntBlk CC TT ops fixed ins k) (getL cnt k)

@[expose] noncomputable def lvlChk (CC : List (List Nat)) (TT : List Nat) (ops : List (List Nat))
    (fixed : List Nat) (b : Nat) (ins : List (Nat × Nat × Nat × List Nat)) : Bool :=
  bAnd(redL fixed, bAnd(redL [b], bAnd(matsOK ops, bAnd(insOK ins, passW CC TT ops fixed ins b))))

@[expose] noncomputable def finChk (CC : List (List Nat)) (ops : List (List Nat)) (fixed : List Nat)
    (b : Nat) (ins : List (Nat × Nat × Nat × List Nat)) (ui : List Nat) : Bool :=
  bAnd(Nat.ble (lenL (stkI CC ops (snoc fixed b) ins [])) (nat_lit 7),
    bAnd(redL ui, invChk (stkI CC ops (snoc fixed b) ins []) ui))

end CFSG.KC.LyG2

end
