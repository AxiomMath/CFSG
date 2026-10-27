module

public import Certificates.Data.Kernel.J4Q.Mat
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KS.SporSch.J3F

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KS

@[expose] noncomputable def packRowsK : List Nat → Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor x (Nat.shiftLeft ih (nat_lit 128)))

@[expose] noncomputable def rows80K (l : List Nat) : Bool :=
  bAnd(Nat.beq l.length (nat_lit 80),
    List.rec (motive := fun _ => Bool) true
      (fun x _ ih => bAnd(Nat.blt x (Nat.shiftLeft (nat_lit 1) (nat_lit 80)), ih)) l)

@[expose] noncomputable def pidxK (i : Nat) : Nat :=
  Nat.sub (Nat.mul (nat_lit 80) i) (Nat.div (Nat.mul i (Nat.sub i (nat_lit 1))) (nat_lit 2))

@[expose] noncomputable def triK (z : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => strictN acc fun a => Nat.lor a (Nat.shiftLeft (Nat.shiftLeft
      (Nat.land (Nat.shiftRight z (pidxK i))
        (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 80) i)) (nat_lit 1))) i)
      (Nat.mul (nat_lit 128) i))) (nat_lit 80)

@[expose] noncomputable def usK : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => strictN acc fun a => Nat.lor a (Nat.shiftLeft
      (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 80)) (Nat.shiftLeft (nat_lit 1) (Nat.succ i)))
      (Nat.mul (nat_lit 128) i))) (nat_lit 80)

@[expose] noncomputable def dgK : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => strictN acc fun a => Nat.lor a (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 129) i)))
    (nat_lit 80)

@[expose] noncomputable def canonK (t0 t1 t2 t3 t4 t5 t6 U D C : Nat) : Nat :=
  strictN C fun x => Nat.lor (Nat.land (Nat.xor x (trJ t0 t1 t2 t3 t4 t5 t6 x)) U) (Nat.land x D)

@[expose] noncomputable def packTriK (rm X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => strictN acc fun a =>
      Nat.lor a (Nat.shiftLeft (Nat.shiftRight (rowJ rm X i) i) (pidxK i))) (nat_lit 80)

@[expose] noncomputable def imgK (c rm t0 t1 t2 t3 t4 t5 t6 U D A AT z : Nat) : Nat :=
  packTriK rm (canonK t0 t1 t2 t3 t4 t5 t6 U D (mulJ c rm AT (mulJ c rm (triK z) A)))

@[expose] noncomputable def formsF (c rm t0 t1 t2 t3 t4 t5 t6 U D : Nat) (F : Nat → Nat)
    (S0 S1 A1 A1T A2 A2T r : Nat) : Bool :=
  CFSG.KC.Enum.strictB (F r) fun w => bAnd(Nat.blt w (Nat.shiftLeft (nat_lit 1) (nat_lit 3240)),
    CFSG.KC.Enum.strictB (pg (nat_lit 13) (mask (nat_lit 13)) S0 r) fun s0 => bAnd(Nat.blt s0 (nat_lit 6156),
    bAnd(Nat.beq (imgK c rm t0 t1 t2 t3 t4 t5 t6 U D A1 A1T (F s0)) w,
    CFSG.KC.Enum.strictB (pg (nat_lit 13) (mask (nat_lit 13)) S1 r) fun s1 => bAnd(Nat.blt s1 (nat_lit 6156),
      Nat.beq (imgK c rm t0 t1 t2 t3 t4 t5 t6 U D A2 A2T (F s1)) w))))

@[expose] noncomputable def hexV (n : Nat) : Nat :=
  nIf(Nat.blt n (nat_lit 58), Nat.sub n (nat_lit 48), Nat.sub n (nat_lit 55))

@[expose] noncomputable def wordsK (F : Nat → Nat) (k b : Nat) (cs : List Char) : Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun cnt _ idx => bAnd(Nat.beq cnt (nat_lit 0), Nat.beq idx k))
    (fun ch _ ih cnt acc idx =>
      CFSG.KC.Enum.strictB (Nat.add (Nat.mul acc (nat_lit 16)) (hexV ch.toNat)) fun a =>
      CFSG.KC.Enum.strictB (Nat.succ cnt) fun cnt' =>
      bIf(Nat.beq cnt' (nat_lit 810),
        bAnd(Nat.beq a (F (Nat.add b idx)), CFSG.KC.Enum.strictB (Nat.succ idx) fun idx' => ih (nat_lit 0) (nat_lit 0) idx'),
        ih cnt' a idx))
    cs (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def hexLK (cs : List Char) : Nat :=
  cs.foldl (fun acc ch => Nat.add (Nat.mul acc (nat_lit 16)) (hexV ch.toNat)) (nat_lit 0)

@[expose] noncomputable def sortK (F SG SGI : Nat → Nat) (n : Nat) : Bool :=
  bAnd(allN (Nat.sub n (nat_lit 1)) fun k => Nat.blt (F (SG k)) (F (SG (Nat.succ k))),
    allN n fun k => CFSG.KC.Enum.strictB (SG k) fun s => bAnd(Nat.blt s n, Nat.beq (SGI s) k))

@[expose] noncomputable def polarK (t0 t1 t2 t3 t4 t5 t6 z : Nat) : Nat :=
  strictN (triK z) fun u => Nat.xor u (trJ t0 t1 t2 t3 t4 t5 t6 u)

@[expose] noncomputable def colK (rm t0 t1 t2 t3 t4 t5 t6 M v : Nat) : Nat :=
  vecJ rm v (trJ t0 t1 t2 t3 t4 t5 t6 M)

@[expose] noncomputable def prodK (c rm D : Nat) (mats : List Nat) (w : List Nat) : Nat :=
  w.foldl (fun M x => mulJ c rm M (CFSG.KC.J4Q.getN (nat_lit 0) mats x)) D

@[expose] noncomputable def combK (c rm D : Nat) (mats : List Nat) (terms : List (List Nat)) : Nat :=
  terms.foldl (fun acc w => Nat.xor acc (prodK c rm D mats w)) (nat_lit 0)

@[expose] noncomputable def spinK (rm t0 t1 t2 t3 t4 t5 t6 : Nat) (mats : List Nat) (v : Nat)
    (tree : List (Nat × Nat)) : List Nat :=
  tree.foldl (fun S t => S ++ [colK rm t0 t1 t2 t3 t4 t5 t6 (CFSG.KC.J4Q.getN (nat_lit 0) mats t.2)
    (CFSG.KC.J4Q.getN (nat_lit 0) S t.1)]) [v]

@[expose] noncomputable def projK (D v k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) D
    (fun i acc => nIf(Nat.beq (Nat.land (Nat.shiftRight v i) (nat_lit 1)) (nat_lit 1),
      Nat.xor acc (Nat.shiftLeft (Nat.shiftLeft (nat_lit 1) k) (Nat.mul (nat_lit 128) i)), acc))
    (nat_lit 80)

@[expose] noncomputable def sepK (c rm t0 t1 t2 t3 t4 t5 t6 D zB RB : Nat) (zs : List Nat)
    (terms : List (List Nat)) (v k P : Nat) (tree : List (Nat × Nat)) (SI : Nat) : Bool :=
  (fun mats => (fun K =>
    bAnd(Nat.beq (mulJ c rm RB (polarK t0 t1 t2 t3 t4 t5 t6 zB)) D,
    bAnd(Nat.blt k (nat_lit 80), bAnd(Nat.beq (Nat.land (Nat.shiftRight v k) (nat_lit 1)) (nat_lit 1),
    bAnd(Nat.beq (colK rm t0 t1 t2 t3 t4 t5 t6 K v) (nat_lit 0),
    bAnd(Nat.beq (mulJ c rm P K) (projK D v k),
    bAnd(Nat.beq tree.length (nat_lit 79),
    bAnd(allN (nat_lit 79) (fun i => bAnd(Nat.ble (tree.getD i (0, 0)).1 i,
      Nat.blt (tree.getD i (0, 0)).2 (nat_lit 4))),
      Nat.beq (mulJ c rm SI (packRowsK (spinK rm t0 t1 t2 t3 t4 t5 t6 mats v tree))) D))))))))
    (combK c rm D mats terms))
    (zs.map fun z => mulJ c rm RB (polarK t0 t1 t2 t3 t4 t5 t6 z))

end CFSG.KS.SporSch.J3F

end
