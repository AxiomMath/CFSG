module

public import Certificates.Data.Kernel.LocalQT.TcP

public section

namespace CFSG.KC.LQT.SP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.LQT.TC

@[expose] noncomputable def getPr (L : List (Int × Int)) (k : Nat) : Int × Int :=
  List.rec (motive := fun _ => Nat → Int × Int) (fun _ => Prod.mk (Int.ofNat 0) (Int.ofNat 0))
    (fun x _ ih k => Nat.rec (motive := fun _ => Int × Int) x (fun j _ => ih j) k) L k

@[expose] noncomputable def lenPr (L : List (Int × Int)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def appPr (L M : List (Int × Int)) : List (Int × Int) :=
  List.rec (motive := fun _ => List (Int × Int)) M (fun x _ ih => List.cons x ih) L

@[expose] noncomputable def revPr (L M : List (Int × Int)) : List (Int × Int) :=
  List.rec (motive := fun _ => List (Int × Int) → List (Int × Int)) (fun M => M)
    (fun x _ ih M => ih (List.cons x M)) L M

@[expose] noncomputable def wordSP (wd : List Int) (b : Nat) : List (Int × Int) × Int :=
  List.rec (motive := fun _ => List (Int × Int) × Int)
    (Prod.mk List.nil (Int.ofNat 0))
    (fun z _ ih => Prod.rec (motive := fun _ => List (Int × Int) × Int)
      (fun ns r => Prod.mk (List.cons (Prod.mk z r) ns)
        (Int.ofNat (Nat.succ (Nat.add b (lenPr ns))))) ih) wd

structure LSt where
  ns : List (Int × Int)
  cnt : Nat
  regs : List Nat
  len : Nat

@[expose] noncomputable def conjsLay (g : Int) (t0 m : Nat) (st : LSt) : LSt :=
  Nat.rec (motive := fun _ => LSt → LSt) (fun st => st)
    (fun i ih st => ih (LSt.mk
      (List.cons (Prod.mk (Int.ofNat (Nat.succ st.cnt)) (Int.neg g))
        (List.cons (Prod.mk g (Int.ofNat (Nat.succ (Nat.add t0 (Nat.sub (Nat.sub m 1) i)))))
          st.ns))
      (Nat.succ (Nat.succ st.cnt)) (List.cons (Nat.succ st.cnt) st.regs) (Nat.succ st.len)))
    m st

@[expose] noncomputable def wordsLay (ws : List (List Int)) (t0 m : Nat) (st : LSt) : LSt :=
  List.rec (motive := fun _ => LSt → LSt) (fun st => st)
    (fun wd _ ih st => ih (Prod.rec (motive := fun _ => LSt)
      (fun ns g => conjsLay g t0 m (LSt.mk (appPr ns st.ns) (Nat.add st.cnt (lenPr ns)) st.regs
        st.len)) (wordSP wd st.cnt))) ws st

@[expose] noncomputable def getN (l : List Nat) (k : Nat) : Nat := getTc (nat_lit 0) l k

@[expose] noncomputable def regRef (regs : List Nat) (len : Nat) (z : Int) : Int :=
  Int.rec (motive := fun _ => Int)
    (fun m => Nat.rec (motive := fun _ => Int) (Int.ofNat 0)
      (fun j _ => Bool.rec (motive := fun _ => Int) (Int.ofNat 0)
        (Int.ofNat (Nat.succ (getN regs (Nat.sub (Nat.sub len j) 1)))) (Nat.blt j len)) m)
    (fun m => Bool.rec (motive := fun _ => Int) (Int.ofNat 0)
        (Int.negSucc (getN regs (Nat.sub (Nat.sub len m) 1))) (Nat.blt m len)) z

@[expose] noncomputable def progLay (prog : List (Int × Int)) (st : LSt) : LSt :=
  List.rec (motive := fun _ => LSt → LSt) (fun st => st)
    (fun pq _ ih st => ih (LSt.mk
      (List.cons (Prod.mk (regRef st.regs st.len pq.1) (regRef st.regs st.len pq.2)) st.ns)
      (Nat.succ st.cnt) (List.cons st.cnt st.regs) (Nat.succ st.len))) prog st

@[expose] noncomputable def layMC (g m : Nat) (ws : List (List Int)) (prog : List (Int × Int)) :
    LSt :=
  progLay prog (wordsLay ws g m (LSt.mk List.nil (Nat.add g m) List.nil (nat_lit 0)))

@[expose] noncomputable def inRegs (g : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil (fun i ih => List.cons i ih) g

@[expose] noncomputable def layRun (g : Nat) (prog : List (Int × Int)) : LSt :=
  progLay prog (LSt.mk List.nil g (inRegs g) g)

@[expose] noncomputable def nodesOf (st : LSt) : List (Int × Int) := revPr st.ns List.nil

@[expose] noncomputable def refSP (idn : Nat) (X XI : Nat → Nat) (z : Int)
    (k : Nat → Nat → Bool) : Bool :=
  Int.rec (motive := fun _ => Bool)
    (fun m => Nat.rec (motive := fun _ => Bool) (k idn idn) (fun j _ => k (X j) (XI j)) m)
    (fun m => k (XI m) (X m)) z

@[expose] noncomputable def refLt (z : Int) (j : Nat) : Bool :=
  Int.rec (motive := fun _ => Bool) (fun m => Nat.ble m j) (fun m => Nat.blt m j) z

@[expose] noncomputable def wfSP (gi : Nat) (D : List (Int × Int)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun ab _ ih j => bAnd(refLt ab.1 j, bAnd(refLt ab.2 j, strictB (Nat.succ j) ih))) D gi

@[expose] noncomputable def letSP (g : Nat) (ws : List (List Int)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun wd _ ih => bAnd(List.rec (motive := fun _ => Bool) true
      (fun z _ ih2 => bAnd(Int.rec (motive := fun _ => Bool) (fun m => Nat.ble m g)
        (fun m => Nat.blt m g) z, ih2)) wd, ih)) ws

@[expose] noncomputable def inSP (IN INI : List Nat) (X XI : Nat → Nat) (j : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → List Nat → Bool)
    (fun _ INI => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) INI)
    (fun x _ ih j INI => List.rec (motive := fun _ => Bool) false
      (fun xi INI' _ => bAnd(Nat.beq (X j) x, bAnd(Nat.beq (XI j) xi, strictB (Nat.succ j)
        fun j' => ih j' INI'))) INI) IN j INI

@[expose] noncomputable def headMC (n w : Nat) (G GI TS TIS : List Nat) (ws : List (List Int))
    (prog : List (Int × Int)) (X XI : Nat → Nat) : Bool :=
  bAnd(idK n w (mask w), bAnd(gensTc n w G GI, bAnd(gensTc n w TS TIS,
    bAnd(inSP G GI X XI (nat_lit 0), bAnd(inSP TS TIS X XI (lenTc G), bAnd(letSP (lenTc G) ws,
      wfSP (Nat.add (lenTc G) (lenTc TS))
        (nodesOf (layMC (lenTc G) (lenTc TS) ws prog))))))))

@[expose] noncomputable def headRun (n w : Nat) (G GI : List Nat) (prog : List (Int × Int))
    (X XI : Nat → Nat) : Bool :=
  bAnd(idK n w (mask w), bAnd(gensTc n w G GI, bAnd(inSP G GI X XI (nat_lit 0),
    wfSP (lenTc G) (nodesOf (layRun (lenTc G) prog)))))

@[expose] noncomputable def nodeSP (n w gi : Nat) (D : List (Int × Int)) (X XI : Nat → Nat)
    (j : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun a b =>
    refSP (pidn n w) X XI a fun A AI => refSP (pidn n w) X XI b fun B BI =>
      bAnd(Nat.beq (X j) (pcomp n w (mask w) A B), Nat.beq (XI j) (pcomp n w (mask w) BI AI)))
    (getPr D (Nat.sub j gi))

@[expose] noncomputable def nodesSP (n w gi : Nat) (D : List (Int × Int)) (X XI : Nat → Nat)
    (lo len : Nat) : Bool :=
  strictB (Nat.add gi (lenPr D)) fun top =>
    allBlk lo (fun j => bIf(bAnd(Nat.ble gi j, Nat.blt j top), nodeSP n w gi D X XI j, true)) len

@[expose] noncomputable def targSP (n w : Nat) (X : Nat → Nat) (regs targets : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun A _ ih => bAnd(canonK n w (mask w) (n * w) A,
      bAnd(List.rec (motive := fun _ => Bool) false
        (fun r _ ih2 => bIf(Nat.beq (X r) A, true, ih2)) regs, ih))) targets

@[expose] noncomputable def targMC (n w g m : Nat) (ws : List (List Int))
    (prog : List (Int × Int)) (X : Nat → Nat) (targets : List Nat) : Bool :=
  targSP n w X (layMC g m ws prog).regs targets

@[expose] noncomputable def selSP (X : Nat → Nat) (regs : List Nat) (len : Nat)
    (idx S : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun S => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) S)
    (fun k _ ih S => List.rec (motive := fun _ => Bool) false
      (fun s S' _ => bAnd(Nat.blt k len,
        bAnd(Nat.beq (X (getN regs (Nat.sub (Nat.sub len k) 1))) s, ih S'))) S) idx S

@[expose] noncomputable def selRun (g : Nat) (prog : List (Int × Int)) (X : Nat → Nat)
    (idx S : List Nat) : Bool :=
  (fun (st : LSt) => selSP X st.regs st.len idx S) (layRun g prog)

end CFSG.KC.LQT.SP

end
