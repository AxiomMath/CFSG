module

public import Certificates.Data.Kernel.LocalQT.Lat
public import Certificates.Data.Kernel.LocalQT.M11

public section

namespace CFSG.KC.LQT.L

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.W CFSG.KC.LQT.S

abbrev Lvl := Nat × List Nat × List Nat × Nat

@[expose] noncomputable def chainF (C : List Lvl) : Nat :=
  List.rec (motive := fun _ => Nat) 1 (fun lv _ ih => Nat.mul lv.2.2.2 ih) C

@[expose] noncomputable def idxM (n : Nat) (C : List Lvl) (F x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun h acc _ => Bool.rec (motive := fun _ => Nat) F acc (Nat.beq h (one n)))
    (fun lv _ ih h acc mult =>
      CFSG.KC.Loop.strictN (img h lv.1) fun j => CFSG.KC.Loop.strictN (getK lv.2.1 j) fun u =>
        Bool.rec (motive := fun _ => Nat)
          (CFSG.KC.Loop.strictN (mul n (inv n u) h) fun h' =>
            ih h' (Nat.add acc (Nat.mul (getK lv.2.2.1 j) mult)) (Nat.mul mult lv.2.2.2))
          F (Nat.beq u 0))
    C x 0 1

@[expose] noncomputable def inC (n : Nat) (C : List Lvl) (F x : Nat) : Bool :=
  Nat.blt (idxM n C F x) F

@[expose] noncomputable def chainOK (n : Nat) (C : List Lvl) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun lv _ ih prev => andB
      (andB (allN n fun j => impB (notB (Nat.beq (getK lv.2.1 j) 0))
          (letB (getK lv.2.1 j) fun u => andB (permK n u)
            (andB (allL prev fun b => Nat.beq (img u b) b)
              (andB (Nat.beq (img u lv.1) j) (Nat.blt (getK lv.2.2.1 j) lv.2.2.2)))))
        (Nat.beq (Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Nat.lor acc
            (Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft 1 (getK lv.2.2.1 j)) 0
              (Nat.beq (getK lv.2.1 j) 0))) n)
          (Nat.sub (Nat.shiftLeft 1 lv.2.2.2) 1)))
      (ih (List.cons lv.1 prev)))
    C []

@[expose] noncomputable def chainFrom (n : Nat) (C : List Lvl) (f : Nat → Bool) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun p => f p)
    (fun lv _ ih p => allN n fun j => impB (notB (Nat.beq (getK lv.2.1 j) 0))
      (letB (mul n p (getK lv.2.1 j)) ih)) C

@[expose] noncomputable def allChain (n : Nat) (C : List Lvl) (f : Nat → Bool) : Bool :=
  chainFrom n C f (one n)

@[expose] noncomputable def chainChunk (n : Nat) (C : List Lvl) (f : Nat → Bool) (j : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) (f (one n))
    (fun lv C' _ => impB (notB (Nat.beq (getK lv.2.1 j) 0))
      (letB (mul n (one n) (getK lv.2.1 j)) (chainFrom n C' f))) C

@[expose] noncomputable def wordsC (n : Nat) (C : List Lvl) (G : List Nat)
    (W : List (List (List Nat))) (d : Nat) : Bool :=
  List.rec (motive := fun _ => List (List (List Nat)) → Nat → Bool) (fun _ _ => true)
    (fun lv _ ih W budget => List.rec (motive := fun _ => Bool) false
      (fun ws W' _ => andB
        (allN n fun j => impB (notB (Nat.beq (getK lv.2.1 j) 0))
          (Nat.beq (evalWK n G (CFSG.KC.LQT.M.getW ws j)) (getK lv.2.1 j)))
        (letB (Nat.rec (motive := fun _ => Nat) 0 (fun j m => Bool.rec (motive := fun _ => Nat) m
            (lenA (CFSG.KC.LQT.M.getW ws j)) (Nat.blt m (lenA (CFSG.KC.LQT.M.getW ws j)))) n)
          fun len => andB (Nat.ble len budget) (ih W' (Nat.sub budget len))))
      W) C W d

@[expose] noncomputable def grpC (n : Nat) (C : List Lvl) (F : Nat) (G : List Nat)
    (W : List (List (List Nat))) (d : Nat) : Bool :=
  andB (allL G (inC n C F)) (andB (wordsC n C G W d)
    (allChain n C fun s => allL G fun g => inC n C F (mul n s g)))

structure SetM where
  mask : Nat
  size : Nat
  elems : List Nat
  ok : Bool

@[expose] noncomputable def memM (n : Nat) (C : List Lvl) (F : Nat) (S : SetM) (x : Nat) : Bool :=
  letB (idxM n C F x) fun i => Nat.blt 0 (Nat.land S.mask (Nat.shiftLeft 1 i))

@[expose] noncomputable def letQ (y : Nat) (k : Nat → SetM × List Nat) : SetM × List Nat :=
  Nat.rec (motive := fun _ => SetM × List Nat) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def addM (n : Nat) (C : List Lvl) (F : Nat) (S : SetM × List Nat)
    (y : Nat) : SetM × List Nat :=
  letQ (idxM n C F y) fun i =>
  Bool.rec (motive := fun _ => SetM × List Nat)
    (Prod.mk (SetM.mk (Nat.lor S.1.mask (Nat.shiftLeft 1 i)) (Nat.succ S.1.size)
      (List.cons y S.1.elems) (andB S.1.ok (Nat.blt i F))) (List.cons y S.2))
    S (Nat.blt 0 (Nat.land S.1.mask (Nat.shiftLeft 1 i)))

@[expose] noncomputable def roundM (n : Nat) (C : List Lvl) (F : Nat) (G : List Nat) (S : SetM)
    (Fr : List Nat) : SetM × List Nat :=
  List.rec (motive := fun _ => SetM × List Nat → SetM × List Nat) (fun st => st)
    (fun x _ ih st => ih (List.rec (motive := fun _ => SetM × List Nat → SetM × List Nat)
      (fun st => st) (fun g _ ih2 st => ih2 (addM n C F st (mul n x g))) G st)) Fr (Prod.mk S [])

@[expose] noncomputable def bfsM (n : Nat) (C : List Lvl) (F : Nat) (G : List Nat) (d : Nat) :
    SetM :=
  (Nat.rec (motive := fun _ => SetM × List Nat)
    (addM n C F (Prod.mk (SetM.mk 0 0 [] true) []) (one n))
    (fun _ st => roundM n C F G st.1 st.2) d).1

@[expose] noncomputable def closedM (n : Nat) (C : List Lvl) (F : Nat) (G : List Nat) (S : SetM) :
    Bool :=
  andB S.ok (andB (memM n C F S (one n))
    (allL S.elems fun x => allL G fun g => memM n C F S (mul n x g)))

abbrev Mem := List Nat × Bool × List (List (List Nat))

abbrev SetX := SetM × Bool

@[expose] noncomputable def mkX (n : Nat) (C : List Lvl) (F d : Nat) (m : Mem) : SetX :=
  Bool.rec (motive := fun _ => SetX) (Prod.mk (bfsM n C F m.1 d) false)
    (Prod.mk (SetM.mk 0 0 [] true) true) m.2.1

@[expose] noncomputable def memX (n : Nat) (C : List Lvl) (F : Nat) (S : SetX) (x : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (memM n C F S.1 x) (inC n C F x) S.2

@[expose] noncomputable def sizeX (F : Nat) (S : SetX) : Nat :=
  Bool.rec (motive := fun _ => Nat) S.1.size F S.2

@[expose] noncomputable def closedX (n : Nat) (C : List Lvl) (F d : Nat) (m : Mem) (S : SetX) :
    Bool :=
  Bool.rec (motive := fun _ => Bool) (closedM n C F m.1 S.1) (grpC n C F m.1 m.2.2 d) S.2

@[expose] noncomputable def eqX (n : Nat) (C : List Lvl) (F : Nat) (EB : SetX) (A B : List Nat)
    (ws : List (List Nat)) : Bool :=
  andB (allL A fun g => memX n C F EB g) (andB (Nat.beq (lenA ws) (lenA B))
    (List.rec (motive := fun _ => List (List Nat) → Bool) (fun _ => true)
      (fun b _ ih ws => List.rec (motive := fun _ => Bool) true
        (fun w ws' _ => andB (Nat.beq (evalWK n A w) b) (ih ws')) ws) B ws))

@[expose] noncomputable def membersX (n : Nat) (C : List Lvl) (F d : Nat) (ms : List Mem) :
    List (Mem × SetX) :=
  List.rec (motive := fun _ => List (Mem × SetX)) []
    (fun m _ ih => List.cons (Prod.mk m (mkX n C F d m)) ih) ms

@[expose] noncomputable def grpM (n : Nat) (C : List Lvl) (F d : Nat) (MG : List Nat)
    (MW : List (List (List Nat))) : Bool :=
  List.rec (motive := fun _ => Bool)
    (andB (closedM n C F MG (bfsM n C F MG d)) (Nat.beq (bfsM n C F MG d).size F))
    (fun _ _ _ => grpC n C F MG MW d) MW

@[expose] noncomputable def closedOKC (n : Nat) (C : List Lvl) (F d : Nat) (MG : List Nat)
    (MW : List (List (List Nat))) (ms : List Mem) : Bool :=
  andB (chainOK n C) (andB (grpM n C F d MG MW)
    (allA (membersX n C F d ms) fun p => closedX n C F d p.1 p.2))

@[expose] noncomputable def coverC (n : Nat) (C : List Lvl) (F : Nat) (ET : SetM)
    (reps : List (Nat × Nat × List (List Nat))) : Bool :=
  andB (allA reps fun r => inC n C F r.1)
  (andB (List.rec (motive := fun _ => Bool) true (fun r rs ih => andB
      (allA rs fun r' => allL ET.elems fun t =>
        notB (memM n C F ET (mul n (mul n (inv n r.1) t) r'.1))) ih) reps)
    (Nat.beq (List.rec (motive := fun _ => Nat) 0 (fun r _ ih => Nat.add ih
      (CFSG.KC.Loop.strictN
        (lenA (filtL ET.elems fun t => memM n C F ET (mul n (mul n (inv n r.1) t) r.1)))
        fun k => Bool.rec (motive := fun _ => Nat) (Nat.add F 1)
          (Nat.div (Nat.mul ET.size ET.size) k)
          (Nat.beq (Nat.mod (Nat.mul ET.size ET.size) k) 0))) reps) F))

@[expose] noncomputable def repsC (n : Nat) (C : List Lvl) (F : Nat) (T : List Nat)
    (mem : List (Mem × SetX)) (reps : List (Nat × Nat × List (List Nat))) : Bool :=
  allA reps fun r => Option.rec (motive := fun _ => Bool) false
    (fun p => eqX n C F p.2 (List.append T [r.1]) p.1.1 r.2.2) (getO mem r.2.1)

@[expose] noncomputable def joinsC (n : Nat) (C : List Lvl) (F : Nat) (mem : List (Mem × SetX))
    (joins : List (Nat × Nat × Nat × List (List Nat))) : Bool :=
  andB (allN (lenA mem) fun a => allN (lenA mem) fun b =>
      anyA joins fun j => andB (Nat.beq j.1 a) (Nat.beq j.2.1 b))
    (allA joins fun j =>
      Option.rec (motive := fun _ => Bool) false (fun pa =>
      Option.rec (motive := fun _ => Bool) false (fun pb =>
      Option.rec (motive := fun _ => Bool) false (fun pc =>
        eqX n C F pc.2 (List.append pa.1.1 pb.1.1) pc.1.1 j.2.2.2)
        (getO mem j.2.2.1)) (getO mem j.2.1)) (getO mem j.1))

@[expose] noncomputable def sizesC (F : Nat) (mem : List (Mem × SetX)) (sizes : List Nat)
    (msz : Nat) : Bool :=
  andB (eqL (List.rec (motive := fun _ => List Nat) []
      (fun p _ ih => List.cons (sizeX F p.2) ih) mem) sizes) (Nat.beq F msz)

@[expose] noncomputable def tleC (n : Nat) (C : List Lvl) (F : Nat) (T : List Nat) : Bool :=
  allL T (inC n C F)

@[expose] noncomputable def tleCC (n : Nat) (C : List Lvl) (d : Nat) (MG : List Nat)
    (MW : List (List (List Nat))) (T : List Nat) : Bool :=
  andB (chainOK n C) (andB (grpM n C (chainF C) d MG MW) (tleC n C (chainF C) T))

@[expose] noncomputable def memsOK (T : List Nat) (lat : List (List Nat)) (ms : List Mem) : Bool :=
  List.rec (motive := fun _ => List Mem → Bool)
    (fun ms => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ms)
    (fun L _ ih ms => List.rec (motive := fun _ => Bool) false
      (fun m ms' _ => andB (eqL m.1 L) (ih ms')) ms) (List.cons T lat) ms

@[expose] noncomputable def latC (n : Nat) (C : List Lvl) (d : Nat) (MG : List Nat)
    (MW : List (List (List Nat))) (T : List Nat) (lat : List (List Nat)) (ms : List Mem)
    (reps : List (Nat × Nat × List (List Nat))) (joins : List (Nat × Nat × Nat × List (List Nat)))
    (sizes : List Nat) (msz : Nat) : Bool :=
  andB (memsOK T lat ms) (andB (closedOKC n C (chainF C) d MG MW ms)
  (andB (coverC n C (chainF C) (bfsM n C (chainF C) T d) reps)
  (andB (repsC n C (chainF C) T (membersX n C (chainF C) d ms) reps)
  (andB (joinsC n C (chainF C) (membersX n C (chainF C) d ms) joins)
  (andB (sizesC (chainF C) (membersX n C (chainF C) d ms) sizes msz)
    (tleC n C (chainF C) T))))))

@[expose] noncomputable def ctC (n : Nat) (C : List Lvl) (F d : Nat) (H N : List Nat) (e : Nat) :
    Bool :=
  allBs
  [closedM n C F H (bfsM n C F H d), closedM n C F N (bfsM n C F N d),
   allL N fun x => memM n C F (bfsM n C F H d) x,
   allL (bfsM n C F H d).elems (fun r => allL N fun x =>
     anyL (bfsM n C F N d).elems fun x' => Nat.beq (mul n r x) (mul n x' r)),
   allL (bfsM n C F H d).elems (fun r =>
     orB (notB (allL N fun x => Nat.beq (mul n r x) (mul n x r))) (memM n C F (bfsM n C F N d) r)),
   Nat.beq (bfsM n C F N d).size (Nat.pow 2 e)]

@[expose] noncomputable def memberC (n : Nat) (C : List Lvl) (d : Nat) (T : List Nat)
    (lat : List (List Nat)) (ms : List Mem) (msz : Nat)
    (cts : List (Nat × List Nat × List Nat × Nat)) : Bool :=
  andB (memsOK T lat ms) (andB (chainOK n C) (allA (membersX n C (chainF C) d ms) fun p =>
    andB (closedX n C (chainF C) d p.1 p.2) (orB (Nat.beq (sizeX (chainF C) p.2) msz)
      (anyA cts fun c => andB (eqL c.2.1 p.1.1)
        (ctC n C (chainF C) c.1 c.2.1 c.2.2.1 c.2.2.2)))))

@[expose] noncomputable def commK (n : Nat) (G : List Nat)
    (l : List (List Nat × List Nat × List Nat × List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (one n) (fun q _ ih => mul n
    (mul n (mul n (mul n (evalWK n G q.1) (evalWK n G q.2.1)) (evalWK n G q.2.2.1))
      (evalWK n G q.2.2.2)) ih) l

@[expose] noncomputable def perfK (n : Nat) (G : List Nat)
    (P : List (List (List Nat × List Nat × List Nat × List Nat))) : Bool :=
  andB (Nat.beq (lenA P) (lenA G)) (andB
    (List.rec (motive := fun _ => List (List (List Nat × List Nat × List Nat × List Nat)) → Bool)
      (fun _ => true) (fun g _ ih P => List.rec (motive := fun _ => Bool) true
        (fun p P' _ => andB (Nat.beq (commK n G p) g) (ih P')) P) G P)
    (allA P fun l => allA l fun q =>
      andB (Nat.beq (mul n (evalWK n G q.1) (evalWK n G q.2.2.1)) (one n))
        (Nat.beq (mul n (evalWK n G q.2.1) (evalWK n G q.2.2.2)) (one n))))

@[expose] noncomputable def noSixK (n : Nat) (S : SetM) : Bool :=
  allL S.elems fun x => letB (mul n x x) fun x2 => letB (mul n x2 x) fun x3 =>
    notB (andB (Nat.beq (mul n x3 x3) (one n))
      (andB (notB (Nat.beq x2 (one n))) (notB (Nat.beq x3 (one n)))))

@[expose] noncomputable def adataC (n : Nat) (C : List Lvl) (F d : Nat)
    (A : List Nat × List (List (List Nat × List Nat × List Nat × List Nat))) : Bool :=
  andB (closedM n C F A.1 (bfsM n C F A.1 d)) (andB (Nat.beq (bfsM n C F A.1 d).size 960)
    (andB (perfK n A.1 A.2) (noSixK n (bfsM n C F A.1 d))))

@[expose] noncomputable def latSixC (n : Nat) (C : List Lvl) (d : Nat) (T : List Nat)
    (lat : List (List Nat)) (ms : List Mem) (sizes : List Nat)
    (ds : List (List Nat × List (List (List Nat × List Nat × List Nat × List Nat)))) : Bool :=
  andB (memsOK T lat ms) (andB (chainOK n C) (andB (allA ds (adataC n C (chainF C) d))
    (allN (lenA ms) fun j => orB (notB (Nat.beq (getK sizes j) 1920))
      (Option.rec (motive := fun _ => Bool) false
        (fun p => andB (closedX n C (chainF C) d p.1 p.2)
          (anyA ds fun A => allL A.1 (memX n C (chainF C) p.2)))
        (getO (membersX n C (chainF C) d ms) j)))))

@[expose] noncomputable def closed7 (C : List Lvl) (d : Nat) (G : List Nat) : Bool :=
  andB (chainOK 7 C) (closedM 7 C (chainF C) G (bfsM 7 C (chainF C) G d))

@[expose] noncomputable def sizes7 (C : List Lvl) (d : Nat) (Ls : List (List Nat)) (N : List Nat) :
    Bool :=
  andB (chainOK 7 C) (andB (allA Ls fun G => (bfsM 7 C (chainF C) G d).ok)
    (eqL (List.rec (motive := fun _ => List Nat) []
      (fun G _ ih => List.cons (bfsM 7 C (chainF C) G d).size ih) Ls) N))

@[expose] noncomputable def setEqM (a b : SetM) : Bool :=
  andB a.ok (andB b.ok (andB (Nat.beq a.size b.size) (Nat.beq a.mask b.mask)))

@[expose] noncomputable def isLat7 (C : List Lvl) (d : Nat) (G : List Nat) (Ls : List (List Nat)) :
    Bool :=
  andB (chainOK 7 C) (andB (closedM 7 C (chainF C) G (bfsM 7 C (chainF C) G d))
    (anyA Ls fun Z => setEqM (bfsM 7 C (chainF C) G d) (bfsM 7 C (chainF C) Z d)))

@[expose] noncomputable def dc7 (C : List Lvl) (ED : SetM) (r : Nat) : SetM :=
  (List.rec (motive := fun _ => SetM × List Nat) (Prod.mk (SetM.mk 0 0 [] true) [])
    (fun e _ ih => List.rec (motive := fun _ => SetM × List Nat) ih
      (fun f _ ih2 => addM 7 C (chainF C) ih2 (mul 7 (mul 7 e r) f)) ED.elems) ED.elems).1

@[expose] noncomputable def cover7 (C : List Lvl) (d : Nat) (D R : List Nat) : Bool :=
  andB (chainOK 7 C) (andB (bfsM 7 C (chainF C) D d).ok (andB
    (allL R fun r => (dc7 C (bfsM 7 C (chainF C) D d) r).ok)
    (allP 7 fun x => impB (even 7 x)
      (anyL R fun r => memM 7 C (chainF C) (dc7 C (bfsM 7 C (chainF C) D d) r) x))))

@[expose] noncomputable def memIff7 (C : List Lvl) (d : Nat) (G : List Nat) (p : Nat → Bool) :
    Bool :=
  andB (chainOK 7 C) (andB (bfsM 7 C (chainF C) G d).ok (allP 7 fun x => impB (even 7 x)
    (iffB (memM 7 C (chainF C) (bfsM 7 C (chainF C) G d) x) (p x))))

@[expose] noncomputable def rhoIn7 (C : List Lvl) (d : Nat) (V G : List Nat) : Bool :=
  andB (chainOK 7 C) (andB (bfsM 7 C (chainF C) G d).ok (allN 512 fun m =>
    impB (Nat.beq (detK2 m) 1) (memM 7 C (chainF C) (bfsM 7 C (chainF C) G d) (rhoK V m))))

@[expose] noncomputable def containsC (n : Nat) (C : List Lvl) (d : Nat) (T : List Nat)
    (lat : List (List Nat)) (ms : List Mem) (sizes : List Nat) (A : List Nat) (k s : Nat) : Bool :=
  andB (memsOK T lat ms) (andB (chainOK n C) (allN k fun j => orB (notB (Nat.beq (getK sizes j) s))
    (Option.rec (motive := fun _ => Bool) (allL A fun g => Nat.beq g (one n))
      (fun p => andB (closedX n C (chainF C) d p.1 p.2) (allL A (memX n C (chainF C) p.2)))
      (getO (membersX n C (chainF C) d ms) j))))

end CFSG.KC.LQT.L

end
