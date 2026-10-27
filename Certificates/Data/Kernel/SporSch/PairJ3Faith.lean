module

public import Certificates.Data.Kernel.SporSch.PairJ3F2
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KS.SporSch.PF2

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2

@[expose] noncomputable def hexVK (c : Nat) : Nat :=
  nIf(Nat.blt c (nat_lit 58), Nat.sub c (nat_lit 48), Nat.sub c (nat_lit 55))

@[expose] noncomputable def hexRun (d : Nat) (F : Nat → Nat) (e : Nat) (cs : List Char) :
    Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun i j _ => bAnd(Nat.beq i e, Nat.beq j (nat_lit 0)))
    (fun ch _ ih i j acc => strictB i fun i => strictB (Char.toNat ch) fun c =>
      bAnd(Nat.blt c (nat_lit 128),
        strictB (Nat.add (Nat.mul acc (nat_lit 16)) (hexVK c)) fun a =>
        strictB (Nat.succ j) fun j1 =>
          bIf(Nat.beq j1 d, bAnd(Nat.beq a (F i), ih (Nat.succ i) (nat_lit 0) (nat_lit 0)),
            ih i j1 a)))
    cs

@[expose] noncomputable def hexRowsK (d : Nat) (F : Nat → Nat) (lo cnt : Nat) (cs : List Char) :
    Bool :=
  hexRun d F (Nat.add lo cnt) cs lo (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def packP (d U : Nat) : Nat :=
  orN d fun i => Nat.shiftLeft (Nat.shiftRight (rowF d U i) i) (offP d i)

@[expose] noncomputable def formB (d w m A1 A1T A2 A2T P0 P1 : Nat) (F : Nat → Nat) (r : Nat) :
    Bool :=
  strictB (F r) fun z => bAnd(Nat.beq (packP d (triP d z)) z,
    bAnd(pullK d A1 A1T z (F (CFSG.KC.Enum.pg w m P0 r)), pullK d A2 A2T z (F (CFSG.KC.Enum.pg w m P1 r))))

@[expose] noncomputable def formsK (d w m A1 A1T A2 A2T P0 P1 : Nat) (F : Nat → Nat) (lo n : Nat) :
    Bool :=
  CFSG.KC.Enum.allN n fun i => formB d w m A1 A1T A2 A2T P0 P1 F (Nat.add lo i)

@[expose] noncomputable def sortAK (F σ : Nat → Nat) (lo n : Nat) : Bool :=
  CFSG.KC.Enum.allN n fun i => Nat.blt (F (σ (Nat.add lo i))) (F (σ (Nat.succ (Nat.add lo i))))

@[expose] noncomputable def permAK (N : Nat) (σ τ : Nat → Nat) (lo n : Nat) : Bool :=
  CFSG.KC.Enum.allN n fun i => strictB (σ (Nat.add lo i)) fun s =>
    bAnd(Nat.blt s N, Nat.beq (τ s) (Nat.add lo i))

@[expose] noncomputable def strictL (y : Nat) (k : Nat → List (Nat × Nat)) : List (Nat × Nat) :=
  Nat.rec (motive := fun _ => List (Nat × Nat)) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def getPK (L : List (Nat × Nat)) : Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat × Nat) (fun _ => (nat_lit 0, nat_lit 0))
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat × Nat) x (fun k _ => ih k) i) L

@[expose] noncomputable def setPK (L : List (Nat × Nat)) (i : Nat) (p : Nat × Nat) :
    List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => [])
    (fun x xs ih i => Nat.rec (motive := fun _ => List (Nat × Nat)) (p :: xs)
      (fun k _ => x :: ih k) i) L i

@[expose] noncomputable def pivGo (d c : Nat) (L : List (Nat × Nat)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => d)
    (fun x _ ih i => Prod.rec (motive := fun _ => Nat)
      (fun a _ => nIf(bAnd(Nat.ble c i, bit a c), i, ih (Nat.succ i))) x) L

@[expose] noncomputable def pivK (d c : Nat) (L : List (Nat × Nat)) : Nat := pivGo d c L (nat_lit 0)

@[expose] noncomputable def elimGo (c ap rp : Nat) (L : List (Nat × Nat)) : Nat → List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => [])
    (fun x _ ih i => Prod.rec (motive := fun _ => List (Nat × Nat))
      (fun a r => Bool.rec (motive := fun _ => List (Nat × Nat)) ((a, r) :: ih (Nat.succ i))
        ((Nat.xor a ap, Nat.xor r rp) :: ih (Nat.succ i))
        (bAnd(Bool.rec (motive := fun _ => Bool) true false (Nat.beq i c), bit a c))) x) L

@[expose] noncomputable def elimK (c ap rp : Nat) (L : List (Nat × Nat)) : List (Nat × Nat) :=
  elimGo c ap rp L (nat_lit 0)

@[expose] noncomputable def colK (d c : Nat) (L : List (Nat × Nat)) : List (Nat × Nat) :=
  strictL (pivK d c L) fun p =>
    Bool.rec (motive := fun _ => List (Nat × Nat)) L
      (Prod.rec (motive := fun _ => List (Nat × Nat))
        (fun ap rp => elimK c ap rp (setPK (setPK L p (getPK L c)) c (ap, rp))) (getPK L p))
      (Nat.blt p d)

@[expose] noncomputable def initGo (d M : Nat) : Nat → Nat → List (Nat × Nat) :=
  Nat.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => [])
    (fun _ ih k => (rowF d M k, pw2 k) :: ih (Nat.succ k))

@[expose] noncomputable def initK (d M : Nat) : List (Nat × Nat) := initGo d M d (nat_lit 0)

@[expose] noncomputable def eqLK (L : List (Nat × Nat)) : List (Nat × Nat) → Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → Bool)
    (fun L' => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L')
    (fun p _ ih L' => List.rec (motive := fun _ => Bool) false
      (fun q qs _ => Prod.rec (motive := fun _ => Bool) (fun a b => Prod.rec (motive := fun _ => Bool)
        (fun a' b' => bAnd(Nat.beq a a', bAnd(Nat.beq b b', ih qs))) q) p) L') L

@[expose] noncomputable def finGo (d X : Nat) (L : List (Nat × Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i d)
    (fun p _ ih i => Prod.rec (motive := fun _ => Bool)
      (fun _ r => bAnd(Nat.beq r (rowF d X i), ih (Nat.succ i))) p) L

@[expose] noncomputable def finK (d X : Nat) (L : List (Nat × Nat)) : Bool := finGo d X L (nat_lit 0)

@[expose] noncomputable def rowsGo (d M : Nat) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i d)
    (fun x _ ih i => bAnd(Nat.beq x (rowF d M i), ih (Nat.succ i))) L

@[expose] noncomputable def rowsEqK (d M : Nat) (L : List Nat) : Bool :=
  bAnd(Nat.blt M (pw2 (Nat.mul d d)), rowsGo d M L (nat_lit 0))

@[expose] noncomputable def mvK (d MT v : Nat) : Nat := vmF d MT v

@[expose] noncomputable def getNK (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun k _ => ih k) i) L

@[expose] noncomputable def prodK (d : Nat) (Ts : List Nat) (ws : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun x _ ih acc => strictN (mulF d acc (getNK Ts x)) fun acc' => ih acc') ws (idF d)

@[expose] noncomputable def combK (d : Nat) (Ts : List Nat) (terms : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun t _ ih => Nat.xor (prodK d Ts t) ih) terms

@[expose] noncomputable def projK (d v k : Nat) : Nat :=
  orN d fun i => Nat.shiftLeft (Nat.xor (pw2 i) (nIf(bit v i, pw2 k, nat_lit 0))) (Nat.mul d i)

@[expose] noncomputable def spinK (d nm : Nat) (TTs : List Nat) (PS : Nat) (tree : List (Nat × Nat)) :
    Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq (Nat.succ i) d)
    (fun t _ ih i => Prod.rec (motive := fun _ => Bool) (fun p r =>
      bAnd(Nat.ble p i, bAnd(Nat.blt r nm,
        bAnd(Nat.beq (rowF d PS (Nat.succ i)) (mvK d (getNK TTs r) (rowF d PS p)), ih (Nat.succ i)))))
      t) tree

@[expose] noncomputable def lenNK (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def tsK (d : Nat) (Ts : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun TT => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) TT)
    (fun t _ ih TT => List.rec (motive := fun _ => Bool) false
      (fun u us _ => bAnd(Nat.beq (trP d t) u, ih us)) TT) Ts

@[expose] noncomputable def colB (d A j : Nat) : Nat :=
  orN d fun i => Nat.shiftLeft (nIf(bit (rowF d A i) j, nat_lit 1, nat_lit 0)) i

@[expose] noncomputable def trB (d A : Nat) : Nat :=
  orN d fun j => Nat.shiftLeft (colB d A j) (Nat.mul d j)

@[expose] noncomputable def polarP (d z : Nat) : Nat :=
  strictN (triP d z) fun U => Nat.xor U (trB d U)

@[expose] noncomputable def sepK (d nm : Nat) (Ts TTs : List Nat) (terms : List (List Nat))
    (v k K KT PP PS PX : Nat) (tree : List (Nat × Nat)) : Bool :=
  bAnd(Nat.beq (lenNK Ts) nm, bAnd(tsK d Ts TTs,
  bAnd(Nat.blt k d, bAnd(bit v k, bAnd(Nat.beq K (combK d Ts terms),
    bAnd(Nat.beq (trP d K) KT, bAnd(Nat.beq (mvK d KT v) (nat_lit 0),
    bAnd(Nat.beq (mulF d PP K) (projK d v k), bAnd(Nat.beq (rowF d PS (nat_lit 0)) v,
    bAnd(spinK d nm TTs PS tree (nat_lit 0), Nat.beq (mulF d PX PS) (idF d)))))))))))

end CFSG.KS.SporSch.PF2

end
