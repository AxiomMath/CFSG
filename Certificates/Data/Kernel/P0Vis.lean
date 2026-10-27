module

public import Certificates.Data.Kernel.P0Orb
public import Certificates.Data.CFSGNative.MonsterB.P0Rank

public section

namespace CFSG.KC.P0Vis

open CFSG.KC.P0Orb MonsterB.P0Rank

@[expose] def m1024 : Nat := 2 ^ 1024 - 1

@[expose] def m32 : Nat := 4294967295

@[expose] noncomputable def bAct (BT κ x : Nat) : Nat := pAct 9 511 9 (fld BT (96 * κ) m96) x

@[expose] noncomputable def rowB (p : Nat) (xs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun x _ ih => Nat.lor (pAct 9 511 9 p x) (Nat.shiftLeft ih 9)) xs

@[expose] noncomputable def btOK (BT : Nat) (BG : List (List Nat)) (t : Nat) : Bool :=
  (List.range (2 ^ t)).all fun κ =>
    Nat.beq (fld BT (96 * (κ + 2 ^ t)) m96) (rowB (fld BT (96 * κ) m96) (BG.getD t []))

@[expose] noncomputable def bt0OK (BT : Nat) (BG : List (List Nat)) : Bool :=
  Nat.beq (fld BT 0 m96) ((List.range 9).foldl (fun a j => a ||| 2 ^ (10 * j)) 0) &&
    Nat.beq BG.length 10 && BG.all (fun cs => Nat.beq cs.length 9) && Nat.blt BT (2 ^ 98304)

@[expose] noncomputable def maskB (f : Nat → Bool) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k ih => Nat.lor ih (bif f k then Nat.shiftLeft 1 k else 0)) n

@[expose] def vO (RT o : Nat) : Nat := fld (slot RT o) 0 65535

@[expose] noncomputable def faOK (FA AT RT o : Nat) : Bool :=
  Nat.beq (fld FA (1024 * o) m1024) (maskB (fun κ => Nat.beq (aAct AT κ (vO RT o)) (vO RT o)) 1024)

@[expose] noncomputable def fbOK (FB BT z : Nat) : Bool :=
  Nat.beq (fld FB (1024 * z) m1024) (maskB (fun κ => Nat.beq (bAct BT κ (emb z)) (emb z)) 1024)

@[expose] def lowM (j : Nat) : Nat :=
  [1431655765, 858993459, 252645135, 16711935, 65535].getD j 0

@[expose] def swp (m j : Nat) : Nat :=
  Nat.lor (Nat.shiftLeft (Nat.land m (lowM j)) (2 ^ j)) (Nat.land (Nat.shiftRight m (2 ^ j)) (lowM j))

@[expose] def swc (m v j : Nat) : Nat :=
  bif Nat.beq (Nat.land (Nat.shiftRight v j) 1) 1 then swp m j else m

@[expose] def clo (m v : Nat) : Nat :=
  Nat.lor m (swc (swc (swc (swc (swc m v 0) v 1) v 2) v 3) v 4)

@[expose] noncomputable def ycRow (YE NY m : Nat) (row : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun j _ ih v => Nat.blt j NY && Nat.beq (fld YE (32 * j) m32) (clo m v) && ih (v + 1)) row

@[expose] noncomputable def ycRows (YE NY : Nat) : Nat → List (List Nat) → Bool
  | _, [] => true
  | i, row :: rows => Nat.beq row.length 32 && ycRow YE NY (fld YE (32 * i) m32) row 0 &&
      ycRows YE NY (i + 1) rows

@[expose] noncomputable def ycOK (YE NY : Nat) (YC : List (List Nat)) : Bool :=
  Nat.beq (fld YE 0 m32) 1 && Nat.beq YC.length NY && ycRows YE NY 0 YC

@[expose] def pcStep (x w : Nat) : Nat :=
  Nat.land x (m1024 / (2 ^ (2 * w) - 1) * (2 ^ w - 1)) +
    Nat.land (Nat.shiftRight x w) (m1024 / (2 ^ (2 * w) - 1) * (2 ^ w - 1))

@[expose] def pc (x : Nat) : Nat :=
  pcStep (pcStep (pcStep (pcStep (pcStep (pcStep (pcStep (pcStep (pcStep (pcStep x 1) 2) 4) 8)
    16) 32) 64) 128) 256) 512

@[expose] noncomputable def cuOf (FB e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) m1024
    (fun z ih => Nat.land ih (bif Nat.beq (Nat.land (Nat.shiftRight e z) 1) 1 then
      fld FB (1024 * z) m1024 else m1024)) 32

abbrev YEnt := Nat × Nat × Nat

@[expose] noncomputable def ygEnts (YE FB s : Nat) : Nat → List YEnt → Option Nat
  | i, [] => some i
  | i, e :: es => bif Nat.beq e.1 i && Nat.beq (pc (fld YE (32 * i) m32)) (2 ^ s) &&
      Nat.beq e.2.1 (cuOf FB (fld YE (32 * i) m32)) && Nat.beq e.2.2 (pc e.2.1) then
      ygEnts YE FB s (i + 1) es else none

@[expose] noncomputable def ygGroups (YE FB NY : Nat) : Nat → Nat → List (List YEnt) → Bool
  | _, i, [] => Nat.beq i NY
  | s, i, g :: gs => Option.rec (motive := fun _ => Bool) false
      (fun j => ygGroups YE FB NY (s + 1) j gs) (ygEnts YE FB s i g)

@[expose] noncomputable def ygOK (YE FB NY : Nat) (YG : List (List YEnt)) : Bool :=
  Nat.beq YG.length 6 && ygGroups YE FB NY 0 0 YG

@[expose] noncomputable def lamBOK (BT : Nat) : Bool :=
  (List.range 1024).all fun κ => [1, 2, 12, 48].all fun l => Nat.beq (bAct BT κ l) l

@[expose] def lamC (τ : Nat) : Nat :=
  Nat.land τ 7 + 8 * Nat.land (Nat.shiftRight τ 4) 1

@[expose] def lamZ (τ : Nat) : Nat :=
  Nat.land (Nat.xor (Nat.shiftRight τ 2) (Nat.shiftRight τ 3)) 1 +
    2 * Nat.land (Nat.xor (Nat.shiftRight τ 4) (Nat.shiftRight τ 5)) 1 + 4 * Nat.shiftRight τ 6

@[expose] noncomputable def lamSpan : Bool :=
  (List.range 512).all fun τ => Nat.blt (lamC τ) 16 && Nat.blt (lamZ τ) 32 &&
    Nat.beq (Nat.xor (colsAct [1, 2, 12, 48] (lamC τ)) (emb (lamZ τ))) τ

@[expose] def uK (κ : Nat) : (Nat × Nat) × Nat := ((0, 0), κ)

@[expose] noncomputable def fval (dat : Data) (key : Nat) : Nat :=
  let kind := Nat.land key 3
  let κ := Nat.land (Nat.shiftRight key 2) 1023
  let x := Nat.shiftRight key 12
  bif Nat.beq kind 0 then (pmul dat (uK κ) (uK κ)).1.1
  else bif Nat.beq kind 1 then
    (lmul dat.beta (pmul dat (uK κ) (uK x)).1 (linv dat.beta (pmul dat (uK x) (uK κ)).1)).1
  else (conjkap dat κ (x, 0)).2

@[expose] noncomputable def factOK (dat : Data) (FK FC i : Nat) : Bool :=
  Nat.beq (fld FC (16 * i) 65535) (fval dat (fld FK (32 * i) m32))

@[expose] def pf (x s : Nat) : Nat := Nat.xor x (Nat.shiftRight x s)

@[expose] def par16 (x : Nat) : Nat := Nat.land (pf (pf (pf (pf x 8) 4) 2) 1) 1

@[expose] noncomputable def tr (f : Nat → Nat) (K n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun e ih => Nat.lor ih (Nat.shiftLeft (par16 (Nat.land K (f e))) e)) n

@[expose] noncomputable def tA (p K : Nat) : Nat :=
  tr (fun e => Nat.xor (Nat.shiftLeft 1 e) (fld p (16 * e) 65535)) K 16

@[expose] noncomputable def tB (p K : Nat) : Nat :=
  tr (fun e => Nat.xor (Nat.shiftLeft 1 e) (fld p (9 * e) 511)) K 9

@[expose] noncomputable def tBeta (P K : Nat) : Nat := tr (fun e => fld P (9 * e) 511) K 16

abbrev Blk := Nat × Nat × Nat × Nat × Nat

@[expose] noncomputable def blkKey (FK : Nat) (ds ks : List Nat) (b : Blk) : Bool :=
  let kind := b.1
  let j := b.2.1
  let k := b.2.2.1
  Nat.blt j ks.length &&
    (bif Nat.beq kind 0 then Nat.beq (fld FK (32 * b.2.2.2.1) m32) (4 * ks.getD j 0)
     else bif Nat.beq kind 1 then Nat.blt j k && Nat.blt k ks.length &&
       Nat.beq (fld FK (32 * b.2.2.2.1) m32) (1 + 4 * ks.getD j 0 + 4096 * ks.getD k 0)
     else Nat.beq kind 2 && Nat.blt k ds.length &&
       Nat.beq (fld FK (32 * b.2.2.2.1) m32) (2 + 4 * ks.getD j 0 + 4096 * ds.getD k 0))

@[expose] noncomputable def blkVal (AT BT BC FC : Nat) (ds ks : List Nat) (b : Blk) : Nat :=
  let kind := b.1
  let j := b.2.1
  let k := b.2.2.1
  let K := b.2.2.2.2
  let r := par16 (Nat.land K (fld FC (16 * b.2.2.2.1) 65535))
  bif Nat.beq kind 0 then
    Nat.xor r (Nat.shiftLeft (tA (fld AT (256 * ks.getD j 0) m256) K) (16 * j + 1))
  else bif Nat.beq kind 1 then
    Nat.xor (Nat.xor r (Nat.shiftLeft (tA (fld AT (256 * ks.getD k 0) m256) K) (16 * j + 1)))
      (Nat.shiftLeft (tA (fld AT (256 * ks.getD j 0) m256) K) (16 * k + 1))
  else
    Nat.xor (Nat.xor r
      (Nat.shiftLeft (tBeta (pAct 144 m144 16 BC (ds.getD k 0)) K) (16 * j + 1)))
      (Nat.shiftLeft (tB (fld BT (96 * ks.getD j 0) m96) K) (16 * (ks.length + k) + 1))

@[expose] noncomputable def farkOK (AT BT BC FK FC : Nat) (ds ks : List Nat) (bl : List Blk) :
    Bool :=
  bl.all (blkKey FK ds ks) &&
    Nat.beq (bl.foldl (fun acc b => Nat.xor acc (blkVal AT BT BC FC ds ks b)) 0) 1

abbrev Cfg := List Nat × List Blk

abbrev Cand := List Nat × List Cfg

@[expose] noncomputable def cfgsOK (AT BT BC FK FC : Nat) (ds g : List Nat) : Nat → List Cfg → Bool
  | _, [] => true
  | φ, c :: cs => c.1.all (fun x => Nat.beq (par16 (Nat.land φ x)) 0) &&
      farkOK AT BT BC FK FC ds (c.1.map (lAct g)) c.2 && cfgsOK AT BT BC FK FC ds g (φ + 1) cs

@[expose] noncomputable def candOK (AT BT BC FK FC : Nat) (ds : List Nat) (a M' nM' : Nat)
    (c : Cand) : Bool :=
  let n := bif Nat.ble (a * nM') 32768 then 1 else bif Nat.ble (a * nM') 65536 then 2 ^ c.1.length
    else 0
  Nat.ble 1 n && c.1.all (fun κ => Nat.beq (Nat.land (Nat.shiftRight M' κ) 1) 1) &&
    Nat.beq c.2.length n && cfgsOK AT BT BC FK FC ds c.1 0 c.2

structure Ctx where
  AT : Nat
  BT : Nat
  BC : Nat
  FK : Nat
  FC : Nat

@[expose] noncomputable def entV (C : Ctx) (ds : List Nat) (a M : Nat) (e : YEnt)
    (cands : List Cand) : Option (List Cand) :=
  bif Nat.ble (a * e.2.2) 16384 then some cands else
    let M' := Nat.land M e.2.1
    let n := pc M'
    bif Nat.ble (a * n) 16384 then some cands else
      List.rec (motive := fun _ => Option (List Cand)) none
        (fun c rest _ => bif candOK C.AT C.BT C.BC C.FK C.FC ds a M' n c then some rest else none)
        cands

@[expose] noncomputable def entsV (C : Ctx) (ds : List Nat) (a M : Nat) :
    List YEnt → List Cand → Option (List Cand) :=
  List.rec (motive := fun _ => List Cand → Option (List Cand)) (fun cands => some cands)
    (fun e _ ih cands => Option.rec (motive := fun _ => Option (List Cand)) none ih
      (entV C ds a M e cands))

@[expose] noncomputable def grpsV (C : Ctx) (ds : List Nat) (d M nM : Nat) :
    Nat → List (List YEnt) → List Cand → Option (List Cand)
  | _, [], cands => some cands
  | s, g :: gs, cands =>
    let a := 2 ^ (d + 4 + s)
    bif Nat.ble (a * nM) 16384 then grpsV C ds d M nM (s + 1) gs cands else
      Option.rec (motive := fun _ => Option (List Cand)) none
        (fun cands' => grpsV C ds d M nM (s + 1) gs cands') (entsV C ds a M g cands)

@[expose] noncomputable def labsOK (AT RT : Nat) : List Nat → List (Nat × Nat) → Bool
  | [], [] => true
  | b :: bs, l :: ls => Nat.blt l.1 68 && Nat.blt l.2 1024 &&
      Nat.beq (aAct AT l.2 (vO RT l.1)) b && labsOK AT RT bs ls
  | _, _ => false

@[expose] noncomputable def fixOf (FA : Nat) (labs : List (Nat × Nat)) : Nat :=
  labs.foldl (fun m l => Nat.land m (fld FA (1024 * l.1) m1024)) m1024

abbrev VRow := List (Nat × Nat) × List Cand

@[expose] noncomputable def visitOK (C : Ctx) (RT FA : Nat) (YG : List (List YEnt)) (r : Nat)
    (row : VRow) : Bool :=
  let s := slot RT r
  let bs := sbasis s
  let M := fixOf FA row.1
  labsOK C.AT RT bs row.1 &&
    Option.rec (motive := fun _ => Bool) false (fun l => l.isEmpty)
      (grpsV C bs (Nat.shiftRight s 80) M (pc M) 0 YG row.2)

@[expose] noncomputable def visitsOK (C : Ctx) (RT FA : Nat) (YG : List (List YEnt)) :
    Nat → List VRow → Bool
  | _, [] => true
  | r, row :: rows => visitOK C RT FA YG r row && visitsOK C RT FA YG (r + 1) rows

@[expose] noncomputable def vgrpOK (C : Ctx) (RT FA : Nat) (YG : List (List YEnt)) (lo g : Nat)
    (rows : List VRow) (i : Nat) : Bool :=
  visitsOK C RT FA YG (lo + g * i) ((rows.drop (g * i)).take g)

end CFSG.KC.P0Vis

end
