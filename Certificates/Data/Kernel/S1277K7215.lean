module

public import Certificates.Data.Kernel.S1277K7214

public section

namespace CFSG.KC.C7215

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277ML CFSG.KC.S1277Gm CFSG.KC.C7214

@[expose] noncomputable def pw4B (B : B6) (k : B6 → Bool) : Bool :=
  forceB (compK B B6.id) fun b1 => forceB (compK B b1) fun b2 => forceB (compK b2 b2) k

@[expose] noncomputable def pw5B (B : B6) (k : B6 → Bool) : Bool :=
  pw4B B fun b4 => forceB (compK B b4) k

@[expose] noncomputable def invB (B : B6) (k : B6 → Bool) : Bool :=
  forceB (compK B B6.id) fun b1 => forceB (compK B b1) fun b2 => forceB (compK B b2) fun b3 =>
    forceB (compK b3 b3) fun b6 => forceB (compK b6 b6) fun b12 => forceB (compK b12 b2) fun b14 =>
    forceB (compK b3 b12) fun b15 => forceB (compK b15 b14) fun b29 =>
    forceB (compK b15 b15) fun b30 => forceB (compK b30 b29) k

@[expose] noncomputable def twoK (B : B6) : Bool := pw4B B fun b4 => beqB b4 B6.id

@[expose] noncomputable def ord3K (B : B6) : Bool := andB (beqB (powK B 3) B6.id) (notB (beqB B B6.id))

@[expose] noncomputable def conjK (g x : B6) (k : B6 → Bool) : Bool :=
  invB g fun gi => forceB (compK (compK g x) gi) k

@[expose] noncomputable def beqMc (A C : Mc) : Bool :=
  andB (Nat.beq A.c0 C.c0) (andB (Nat.beq A.c1 C.c1) (Nat.beq A.c2 C.c2))

@[expose] noncomputable def memMc (A : Mc) (L : List Mc) : Bool := anyG (beqMc A) L

@[expose] noncomputable def validMc (A : Mc) : Bool :=
  andB (Nat.blt A.c0 (nat_lit 64)) (andB (Nat.blt A.c1 (nat_lit 64)) (Nat.blt A.c2 (nat_lit 64)))

@[expose] noncomputable def maskMc (I : List ℕ) (L : List Mc) (m : ℕ) : Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun m => allL (fun n => bitN m n) I)
    (fun A _ r m => Bool.rec (motive := fun _ => Bool) (r m)
      (strictB (Nat.lor m (Nat.shiftLeft (nat_lit 1) (Nat.add A.c0 (Nat.add (Nat.mul (nat_lit 64)
        A.c1) (Nat.mul (nat_lit 4096) A.c2))))) r) (validMc A)) L m

@[expose] noncomputable def forceMc (A : Mc) (k : Mc → Bool) : Bool :=
  strictB A.c0 fun a => strictB A.c1 fun b => strictB A.c2 fun c => k ⟨a, b, c⟩

@[expose] noncomputable def addS (gens : List Mc) (x : Mc) (k : ℕ → List Mc → Bool) :
    ℕ → List Mc → Bool :=
  List.rec (motive := fun _ => ℕ → List Mc → Bool) k (fun g _ r s l => forceMc (mulF x g) fun y =>
    Bool.rec (motive := fun _ => Bool) (strictB (insS s (mcIdx y)) fun s' => r s' (y :: l)) (r s l)
      (memS s (mcIdx y))) gens

@[expose] noncomputable def foldS (gens fr : List Mc) (k : ℕ → List Mc → Bool) :
    ℕ → List Mc → Bool :=
  List.rec (motive := fun _ => ℕ → List Mc → Bool) k (fun x _ r => addS gens x r) fr

@[expose] noncomputable def bfsS (gens : List Mc) (n : ℕ) (k : List Mc → Bool) :
    ℕ → List Mc → List Mc → Bool :=
  Nat.rec (motive := fun _ => ℕ → List Mc → List Mc → Bool) (fun _ al _ => k al)
    (fun _ r s al fr => List.rec (motive := fun _ => Bool) (k al)
      (fun _ _ _ => foldS gens fr (fun s' nw => r s' (al ++ nw) nw) s []) fr) n

@[expose] noncomputable def genK (I : List ℕ) (gens : List Mc) : Bool :=
  bfsS gens 64 (fun cl => maskMc I cl (nat_lit 0)) (insS 0 (mcIdx Mc.one)) [Mc.one] [Mc.one]

@[expose] noncomputable def samePL (A C : Mc) : Bool :=
  andB (eqB (presvK p1c (Mc.toB6 A)) (presvK p1c (Mc.toB6 C)))
    (eqB (presvK l2c (Mc.toB6 A)) (presvK l2c (Mc.toB6 C)))

@[expose] def ga : B6 := Mc.toB6 ⟨8, 16, 63⟩

@[expose] def gb : B6 := Mc.toB6 ⟨1, 12, 39⟩

@[expose] noncomputable def ck1 (G : List B6) : Bool :=
  andB (memB ga G) (andB (memB gb G) (allG (fun B => orB (memB B zs6)
    (orB (notB (beqB (compK B ga) (compK ga B))) (notB (beqB (compK B gb) (compK gb B))))) G))

@[expose] noncomputable def ckN (P R : List B6) : Bool :=
  allG (fun g => invB g fun gi => allG (fun r => memB (compK (compK g r) gi) R) R) P

@[expose] noncomputable def ckT (P R : List B6) : Bool :=
  allG (fun u => orB (notB (twoK u)) (orB (memB u R)
    (anyG (fun g => conjK g u fun c => notB (twoK (compK u c))) P))) P

@[expose] noncomputable def commM (R : List B6) : ℕ :=
  maskBelow (fun x => anyG (fun r => anyL (fun c => Nat.beq x (Nat.xor c (appK r c)))
    (List.range 64)) R) (nat_lit 64)

@[expose] noncomputable def ck6 : Bool :=
  strictB (commM r2) fun m => allL (fun p => anyG (fun r => anyL (fun c =>
    bitN m (Nat.xor p (Nat.xor c (appK r c)))) (List.range 64)) r2) l2c

@[expose] noncomputable def ck7 : Bool :=
  allL (fun p => anyG (fun s => anyL (fun c => Nat.beq (Nat.xor c (appK s c)) p)
    (List.range 64)) s0) l2c

@[expose] noncomputable def ck8 (P : List B6) : Bool :=
  allL (fun c => orB (memN c p1c) (spanChk (p1c ++ P.map fun g => appK g c) (List.range 64)))
    (List.range 64)

@[expose] noncomputable def ck9 (P : List B6) : Bool :=
  allL (fun c => orB (Nat.beq c 0) (spanHas (P.map fun g => g.app c) p1c)) p1c

@[expose] noncomputable def ck10 (I W : List ℕ) : Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun W => List.rec (motive := fun _ => Bool) true
    (fun _ _ _ => false) W)
    (fun n _ r W => List.rec (motive := fun _ => Bool) false (fun w W' _ =>
      andB (Nat.beq n (Nat.land w (nat_lit 262143)))
        (andB (memMc (Mc.ofIdx (Nat.land (Nat.shiftRight w (nat_lit 18)) (nat_lit 262143))) s0m)
        (andB (memMc (Mc.ofIdx (Nat.shiftRight w (nat_lit 36))) s0m)
        (andB (memMc (mulF (mulF (Mc.ofIdx (Nat.land (Nat.shiftRight w (nat_lit 18))
          (nat_lit 262143))) (Mc.ofIdx n)) (Mc.ofIdx (Nat.shiftRight w (nat_lit 36)))) dreps)
        (andB (samePL (mulF (mulF (Mc.ofIdx (Nat.land (Nat.shiftRight w (nat_lit 18))
          (nat_lit 262143))) (Mc.ofIdx n)) (Mc.ofIdx (Nat.shiftRight w (nat_lit 36)))) (Mc.ofIdx n))
          (r W')))))) W) I W

@[expose] noncomputable def ck11 (I : List ℕ) (D : List Mc) : Bool :=
  allG (fun r => orB (presvK p1c (Mc.toB6 r)) (orB (presvK l2c (Mc.toB6 r)) (genK I (s0m ++ [r]))))
    D

@[expose] noncomputable def ck12 (I : List ℕ) (D : List Mc) : Bool :=
  allG (fun r => orB (presvK p1c (Mc.toB6 r)) (orB (notB (presvK l2c (Mc.toB6 r)))
    (allG (fun r' => orB (notB (presvK p1c (Mc.toB6 r'))) (orB (presvK l2c (Mc.toB6 r'))
      (genK I (s0m ++ [r, r'])))) dreps))) D

@[expose] noncomputable def ckY (P L : List B6) : Bool :=
  allG (fun y => orB (notB (ord3K y)) (orB (memB y zs6) (orB (memB y L)
    (anyG (fun s => conjK s y fun c => andB (invB c fun ci => notB (twoK (compK y ci)))
      (notB (twoK (compK y c)))) s0)))) P

@[expose] noncomputable def ckU (P L : List B6) : Bool :=
  allG (fun u => orB (notB (twoK u)) (orB (memB u L) (allG (fun y => orB (notB (ord3K y))
    (invB y fun yi => orB (notB (twoK (compK u (compK (compK y u) yi))))
      (notB (twoK (compK u (compK (compK yi u) y)))))) L))) P

@[expose] noncomputable def ckO (f : B6 → Bool) (G L : List B6) : Bool :=
  allG (fun g => orB (notB (f g)) (orB (notB (eq15B g)) (memB g L))) G

@[expose] noncomputable def fixP1K (B : B6) : Bool := allL (fun c => Nat.beq (appK B c) c) p1c

@[expose] noncomputable def onQuotK (B : B6) : Bool :=
  andB (presvK l2c B) (allL (fun c => memN (Nat.xor c (appK B c)) l2c) (List.range 64))

@[expose] noncomputable def inLZ (L : List B6) (B : B6) : Bool :=
  anyG (fun a => anyG (fun z => beqB B (compK a z)) zs6) L

@[expose] noncomputable def ckZo (P L : List B6) : Bool :=
  allG (fun g => orB (notB (eq15B g)) (inLZ L g)) P

@[expose] noncomputable def ckZs (P L : List B6) : Bool := allG (fun g => inLZ L (compK g g)) P

@[expose] noncomputable def ck23 (G : List B6) : Bool :=
  allG (fun g => orB (notB (pw5B g fun b => beqB b B6.id)) (orB (beqB g B6.id)
    (allL (fun c => orB (Nat.beq c 0) (orB (memN c oVecL) (notB (Nat.beq (appK g c) c))))
      (List.range 64)))) G

@[expose] noncomputable def ck24 (G : List B6) : Bool :=
  allL (fun c => anyG (fun g => andB (pw5B g fun b => beqB b B6.id) (andB (notB (beqB g B6.id))
    (Nat.beq (appK g c) c))) G) oVecL

@[expose] noncomputable def ck25 (N : List B6) : Bool :=
  allG (fun B => orB (notB (allL (fun p => Nat.beq (pn (appK B p)) p) oPts)) (memB B zs6)) N

end CFSG.KC.C7215

end
