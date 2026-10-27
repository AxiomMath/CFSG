module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModData3
public import Certificates.Data.Kernel.S1277KML

public section

namespace CFSG.KC.C7214

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277ML CFSG.KC.S1277Gm

@[expose] noncomputable def allG {α : Type} (f : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ r => andB (f x) r) l

@[expose] noncomputable def anyG {α : Type} (f : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ r => orB (f x) r) l

@[expose] noncomputable def cntG {α : Type} (f : α → Bool) (l : List α) : ℕ :=
  List.rec (motive := fun _ => ℕ) (nat_lit 0) (fun x _ r => Bool.rec (motive := fun _ => ℕ) r
    (Nat.succ r) (f x)) l

@[expose] noncomputable def appK (B : B6) (v : ℕ) : ℕ :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor
    (Nat.mul B.c0 (Nat.land v (nat_lit 1)))
    (Nat.mul B.c1 (bit1 v (nat_lit 1))))
    (Nat.mul B.c2 (bit1 v (nat_lit 2))))
    (Nat.mul B.c3 (bit1 v (nat_lit 3))))
    (Nat.mul B.c4 (bit1 v (nat_lit 4))))
    (Nat.mul B.c5 (bit1 v (nat_lit 5)))

@[expose] noncomputable def compK (B C : B6) : B6 :=
  ⟨appK B C.c0, appK B C.c1, appK B C.c2, appK B C.c3, appK B C.c4, appK B C.c5⟩

@[expose] noncomputable def powK (B : B6) (n : ℕ) : B6 :=
  Nat.rec (motive := fun _ => B6) B6.id (fun _ r => compK B r) n

@[expose] noncomputable def beqB (B C : B6) : Bool :=
  andB (Nat.beq B.c0 C.c0) (andB (Nat.beq B.c1 C.c1) (andB (Nat.beq B.c2 C.c2)
    (andB (Nat.beq B.c3 C.c3) (andB (Nat.beq B.c4 C.c4) (Nat.beq B.c5 C.c5)))))

@[expose] noncomputable def forceB (X : B6) (k : B6 → Bool) : Bool :=
  strictB X.c0 fun a0 => strictB X.c1 fun a1 => strictB X.c2 fun a2 => strictB X.c3 fun a3 =>
    strictB X.c4 fun a4 => strictB X.c5 fun a5 => k ⟨a0, a1, a2, a3, a4, a5⟩

@[expose] noncomputable def validB (B : B6) : Bool :=
  andB (Nat.blt B.c0 (nat_lit 64)) (andB (Nat.blt B.c1 (nat_lit 64)) (andB (Nat.blt B.c2 (nat_lit 64))
    (andB (Nat.blt B.c3 (nat_lit 64)) (andB (Nat.blt B.c4 (nat_lit 64)) (Nat.blt B.c5 (nat_lit 64))))))

@[expose] noncomputable def pow15B (B : B6) (k : B6 → B6 → Bool) : Bool :=
  forceB (compK B B6.id) fun b1 => forceB (compK B b1) fun b2 => forceB (compK B b2) fun b3 =>
    forceB (compK b3 b3) fun b6 => forceB (compK b6 b6) fun b12 => k b3 b12

@[expose] noncomputable def eq15B (B : B6) : Bool := pow15B B fun b3 b12 => beqB (compK b3 b12) B6.id

@[expose] noncomputable def eq60B (B : B6) : Bool :=
  pow15B B fun b3 b12 => forceB (compK b3 b12) fun b15 => forceB (compK b15 b15) fun b30 =>
    beqB (compK b30 b30) B6.id

@[expose] noncomputable def memB (B : B6) (L : List B6) : Bool := anyG (beqB B) L

@[expose] noncomputable def invoB (B : B6) : Bool :=
  andB (beqB (compK B B) B6.id) (notB (beqB B B6.id))

@[expose] noncomputable def fixK (B : B6) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (fun c r => Bool.rec (motive := fun _ => ℕ) r
    (Nat.succ r) (Nat.beq (appK B c) c)) (nat_lit 64)

@[expose] noncomputable def fixMK (B : B6) : ℕ :=
  maskBelow (fun c => Nat.beq (appK B c) c) (nat_lit 64)

@[expose] noncomputable def presvK (l : List ℕ) (B : B6) : Bool :=
  allL (fun c => anyL (fun d => Nat.beq d (appK B c)) l) l

@[expose] noncomputable def memN (c : ℕ) (l : List ℕ) : Bool := anyL (fun d => Nat.beq d c) l

@[expose] noncomputable def ofW (w s : ℕ) : B6 := B6.ofP (Nat.shiftRight w s)

@[expose] noncomputable def chk1 (G : List B6) : Bool :=
  allL (fun c => anyG (fun g => Nat.beq (appK g c) 1) G) oVecL

@[expose] noncomputable def chk2 (G : List B6) : Bool :=
  allL (fun c => orB (Nat.beq c 0) (orB (memN c oVecL)
    (allL (fun d => orB (Nat.beq d 0) (anyG (fun g => Nat.beq (appK g c) d) G)) p1c)))
    (List.range 64)

@[expose] noncomputable def chk3 (G : List B6) : Bool := Nat.beq (cntG (presvK pt1) G) 180

@[expose] noncomputable def chk5 (G : List B6) : Bool :=
  allG (fun g => orB (notB (presvK pt1 g)) (orB (notB (Nat.beq ((g.c2 >>> 2) % 4) 1 &&
    Nat.beq ((g.c4 >>> 2) % 4) 0 && Nat.beq ((g.c2 >>> 4) % 4) 0 && Nat.beq ((g.c4 >>> 4) % 4) 1))
    (beqB g B6.id))) G

@[expose] noncomputable def chk6 (T : List B6) : Bool := allG (fun g => Nat.beq (det2 g) 1) T

@[expose] noncomputable def addSp (m g : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.lor m (maskBelow (fun x => bitN m (Nat.xor x g)) (nat_lit 64)))
    m (bitN m g)

@[expose] noncomputable def spanChk (l ds : List ℕ) : Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun m => allL (fun d => bitN m d) ds)
    (fun g _ r m => andB (Nat.blt g (nat_lit 64)) (strictB (addSp m g) r)) l (nat_lit 1)

@[expose] noncomputable def chk7 (T : List B6) : Bool :=
  allL (fun c => orB (memN c pt1) (spanChk (pt1 ++ T.map fun g => appK g c) (List.range 64)))
    (List.range 64)

@[expose] noncomputable def chk8 (T : List B6) : Bool :=
  spanChk (T.flatMap fun g => (List.range 64).map fun c => c ^^^ appK g c) (List.range 64)

@[expose] noncomputable def cubeB (B : B6) : Bool := beqB (powK B 3) B6.id

@[expose] noncomputable def chk9 (T : List B6) : Bool :=
  allG (fun g => anyG (fun a => andB (cubeB a) (andB (memB (compK (compK a a) g) T)
    (andB (cubeB (compK (compK a a) g)) (beqB g (compK a (compK (compK a a) g)))))) T) T

@[expose] noncomputable def chk10 (T : List B6) (W : List ℕ) : Bool :=
  andB (allG (fun g => anyL (fun w => beqB g (ofW w 0)) W) T)
    (allL (fun w => andB (memB (ofW w 36) T) (andB (memB (ofW w 72) T)
      (beqB (ofW w 0) (compK (compK (compK (ofW w 36) (ofW w 72)) (powK (ofW w 36) 59))
        (powK (ofW w 72) 59))))) W)

@[expose] noncomputable def chk11 (N : List B6) : Bool :=
  allG (fun B => orB (notB (invoB B)) (Nat.ble (fixK B) 16)) N

@[expose] noncomputable def chk12 (N : List B6) : Bool :=
  allG (fun B => andB (validB B)
    (orB (notB (eq15B B)) (orB (beqB B B6.id) (Nat.blt (fixK B) 8)))) N

@[expose] noncomputable def chk13 (N : List B6) : Bool :=
  allG (fun B => orB (notB (invoB B)) (orB (Nat.blt (fixK B) 16)
    (anyL (fun c => Nat.beq (appK B c) c) oVecL))) N

@[expose] noncomputable def chk14 (G : List B6) : Bool :=
  allG (fun B => orB (notB (invoB B)) (strictB (fixMK B) fun m =>
    anyG (fun g => allBelow (fun c => eqB (bitN m c) (Nat.blt (appK g c) 16)) 64) G)) G

@[expose] noncomputable def chk15 (N : List B6) : Bool :=
  allG (fun B => orB (Nat.blt (cntL (fun c => Nat.beq (appK B c) c) l2c) 8) (memB B r2)) N

@[expose] noncomputable def chk16 (S N : List B6) (Y : List ℕ) : Bool :=
  andB (allG (fun y => orB (notB (beqB (compK y y) B6.id)) (anyL (fun w => beqB y (ofW w 0)) Y)) S)
    (allL (fun w => strictB (fldN w 36) fun b1 => strictB (fldN w 42) fun b2 =>
      strictB (fldN w 48) fun b3 =>
      andB (Nat.beq (appK (ofW w 0) b1) b1) (andB (Nat.beq (appK (ofW w 0) b2) b2)
        (andB (Nat.beq (appK (ofW w 0) b3) b3)
          (allG (fun B => orB (notB (andB (Nat.beq (appK B b1) b1) (andB (Nat.beq (appK B b2) b2)
            (Nat.beq (appK B b3) b3)))) (orB (beqB B B6.id) (beqB B (ofW w 0)))) N)))) Y)

@[expose] noncomputable def chk17 (S : List B6) : Bool :=
  allG (fun y => orB (notB (beqB (compK y y) B6.id)) (Nat.beq (fixK y) 8)) S

@[expose] noncomputable def chk18 (S : List B6) : Bool :=
  allG (fun y => orB (notB (beqB (compK y y) B6.id)) (allL (fun p => orB (notB (presvK (ptOf p) y))
    (anyL (fun c => Nat.beq (appK y c) c) oVecL)) oPts)) S

@[expose] noncomputable def s0pK : List B6 := s0 ++ s0.map fun s => compK s sig6

@[expose] noncomputable def chk19 (S : List B6) : Bool :=
  allG (fun t => orB (notB (allG (fun s => anyG (fun s' => beqB (compK t s) (compK s' t)) s0) s0))
    (orB (notB (beqB (powK t 4) B6.id))
      (anyG (fun k => anyG (fun u => beqB (compK k t) (compK u k)) s0pK) zs6))) S

@[expose] noncomputable def prodK (l : List B6) : List B6 := l.flatMap fun a => s0pK.map fun s => compK a s

@[expose] noncomputable def chkCl (L D : List B6) : Bool :=
  andB (allG (fun x => memB x D) L) (andB (allG (fun x => memB x L) D)
    (allG (fun x => allG (fun y => memB (compK x y) D) D) D))

@[expose] noncomputable def chkZ (L C : List B6) (i : B6) : Bool :=
  allG (fun B => orB (notB (allG (fun D => beqB (compK B D) (compK D B)) C))
    (orB (beqB B B6.id) (beqB B i))) L

@[expose] noncomputable def chk24 (S N : List B6) : Bool :=
  allG (fun y => orB (notB (beqB (compK y y) B6.id)) (anyG (fun m =>
    orB (beqB (compK y m) (compK m i1)) (beqB (compK y m) (compK m i2))) N)) S

@[expose] noncomputable def chk25 (N : List B6) : Bool :=
  allG (fun m => notB (beqB (compK i2 m) (compK m i1))) N

@[expose] noncomputable def chk26 (G N : List B6) : Bool :=
  andB (memB i1 N) (andB (notB (memB i1 G)) (andB (memB i2 N) (notB (memB i2 G))))

@[expose] noncomputable def chk27 : Bool := andB (memB i1 (prodK l1)) (memB i2 (prodK l2))

@[expose] noncomputable def chk28 (N : List B6) : Bool := allG (fun B => andB (validB B) (eq60B B)) N

end CFSG.KC.C7214

end
