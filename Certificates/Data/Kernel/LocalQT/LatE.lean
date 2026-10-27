module

public import Certificates.Data.Kernel.LocalQT.PairsH

public section

namespace CFSG.KC.LQT.L

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.W CFSG.KC.LQT.S

@[expose] noncomputable def tabOK (n : Nat) (D : List Lvl) (G : List Nat) (T : List (List Nat))
    (L : Nat) : Bool :=
  andB (allA T fun w => Nat.ble (lenA w) L)
    (Nat.beq (List.rec (motive := fun _ => Nat) 0
        (fun w _ acc => Nat.lor (Nat.shiftLeft 1 (idxM n D (chainF D) (evalWK n G w))) acc) T)
      (Nat.sub (Nat.shiftLeft 1 (chainF D)) 1))

@[expose] noncomputable def wordsT (n : Nat) (C : List Lvl) (G : List Nat)
    (W : List (List (List Nat))) (k : Nat) (T : List (List Nat)) (L d : Nat) : Bool :=
  List.rec (motive := fun _ => List (List (List Nat)) → Nat → Nat → Bool) (fun _ _ _ => true)
    (fun lv C' ih W budget k => Bool.rec (motive := fun _ => Bool)
      (List.rec (motive := fun _ => Bool) false
        (fun ws W' _ => andB
          (allN n fun j => impB (notB (Nat.beq (getK lv.2.1 j) 0))
            (Nat.beq (evalWK n G (CFSG.KC.LQT.M.getW ws j)) (getK lv.2.1 j)))
          (letB (Nat.rec (motive := fun _ => Nat) 0 (fun j m => Bool.rec (motive := fun _ => Nat) m
              (lenA (CFSG.KC.LQT.M.getW ws j)) (Nat.blt m (lenA (CFSG.KC.LQT.M.getW ws j)))) n)
            fun len => andB (Nat.ble len budget) (ih W' (Nat.sub budget len) (Nat.sub k 1))))
        W)
      (andB (Nat.ble L budget) (tabOK n (List.cons lv C') G T L))
      (Nat.beq k 0))
    C W d k

@[expose] noncomputable def grpT (n : Nat) (C : List Lvl) (F : Nat) (G : List Nat)
    (W : List (List (List Nat))) (k : Nat) (T : List (List Nat)) (L d : Nat) : Bool :=
  andB (allL G (inC n C F)) (andB (wordsT n C G W k T L d)
    (CFSG.KC.LQT.PH.simsK n C (List.append G (CFSG.KC.LQT.PH.allReps C))))

abbrev MemG := List Nat × List Lvl × List (List (List Nat))

@[expose] noncomputable def memG (n : Nat) (m : MemG) (x : Nat) : Bool :=
  inC n m.2.1 (chainF m.2.1) x

@[expose] noncomputable def closedMG (n d : Nat) (m : MemG) : Bool :=
  andB (chainOK n m.2.1) (CFSG.KC.LQT.PH.grpS n m.2.1 (chainF m.2.1) m.1 m.2.2 d)

@[expose] noncomputable def eqG (n : Nat) (EB : MemG) (A B : List Nat) (ws : List (List Nat)) :
    Bool :=
  andB (allL A (memG n EB)) (andB (Nat.beq (lenA ws) (lenA B))
    (List.rec (motive := fun _ => List (List Nat) → Bool) (fun _ => true)
      (fun b _ ih ws => List.rec (motive := fun _ => Bool) true
        (fun w ws' _ => andB (Nat.beq (evalWK n A w) b) (ih ws')) ws) B ws))

@[expose] noncomputable def memsOKG (T : List Nat) (lat : List (List Nat)) (ms : List MemG) :
    Bool :=
  List.rec (motive := fun _ => List MemG → Bool)
    (fun ms => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ms)
    (fun L _ ih ms => List.rec (motive := fun _ => Bool) false
      (fun m ms' _ => andB (eqL m.1 L) (ih ms')) ms) (List.cons T lat) ms

@[expose] noncomputable def labOK (n K : Nat) (lab : List Nat) (G : List Nat) : Bool :=
  andB (Nat.beq (lenA lab) n) (andB (allL lab fun v => Nat.blt v K)
    (allL G fun g => allN n fun p => Nat.beq (getK lab (img g p)) (getK lab p)))

@[expose] noncomputable def incK (n K : Nat) (lab : List Nat) (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun p acc => Nat.add acc (Nat.shiftLeft 1
    (Nat.mul 8 (Nat.add (Nat.mul K (getK lab p)) (getK lab (img x p)))))) n

@[expose] noncomputable def coverA (n : Nat) (C : List Lvl) (F : Nat) (Tm : MemG) (K : Nat)
    (lab : List Nat) (reps : List (Nat × Nat × List (List Nat))) : Bool :=
  andB (labOK n K lab Tm.1) (allA reps fun r => inC n C F r.1)

@[expose] noncomputable def coverD (n : Nat) (Tm : MemG) (K : Nat) (lab : List Nat)
    (reps : List (Nat × Nat × List (List Nat))) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r rs ih => andB
    (allA rs fun r' => orB (notB (Nat.beq (incK n K lab r.1) (incK n K lab r'.1)))
      (allChain n Tm.2.1 fun t => notB (memG n Tm (mul n (mul n (inv n r.1) t) r'.1)))) ih) reps

@[expose] noncomputable def coverN (n F : Nat) (Tm : MemG)
    (reps : List (Nat × Nat × List (List Nat))) : Bool :=
  Nat.beq (List.rec (motive := fun _ => Nat) 0 (fun r _ ih => Nat.add ih
    (CFSG.KC.Loop.strictN
      (CFSG.KC.LQT.PH.cntFrom n Tm.2.1 (fun t => memG n Tm (mul n (mul n (inv n r.1) t) r.1))
        (one n))
      fun k => Bool.rec (motive := fun _ => Nat) (Nat.add F 1)
        (Nat.div (Nat.mul (chainF Tm.2.1) (chainF Tm.2.1)) k)
        (Nat.beq (Nat.mod (Nat.mul (chainF Tm.2.1) (chainF Tm.2.1)) k) 0))) reps) F

@[expose] noncomputable def coverG (n : Nat) (C : List Lvl) (F : Nat) (Tm : MemG) (K : Nat)
    (lab : List Nat) (reps : List (Nat × Nat × List (List Nat))) : Bool :=
  andB (coverA n C F Tm K lab reps) (andB (coverD n Tm K lab reps) (coverN n F Tm reps))

@[expose] noncomputable def repsG (n : Nat) (T : List Nat) (ms : List MemG)
    (reps : List (Nat × Nat × List (List Nat))) : Bool :=
  allA reps fun r => Option.rec (motive := fun _ => Bool) false
    (fun m => eqG n m (List.append T [r.1]) m.1 r.2.2) (getO ms r.2.1)

@[expose] noncomputable def joinsG (n : Nat) (ms : List MemG)
    (joins : List (Nat × Nat × Nat × List (List Nat))) : Bool :=
  andB (allN (lenA ms) fun a => allN (lenA ms) fun b =>
      anyA joins fun j => andB (Nat.beq j.1 a) (Nat.beq j.2.1 b))
    (allA joins fun j =>
      Option.rec (motive := fun _ => Bool) false (fun pa =>
      Option.rec (motive := fun _ => Bool) false (fun pb =>
      Option.rec (motive := fun _ => Bool) false (fun pc =>
        eqG n pc (List.append pa.1 pb.1) pc.1 j.2.2.2)
        (getO ms j.2.2.1)) (getO ms j.2.1)) (getO ms j.1))

@[expose] noncomputable def sizesG (F : Nat) (ms : List MemG) (sizes : List Nat) (msz : Nat) :
    Bool :=
  andB (eqL (List.rec (motive := fun _ => List Nat) []
      (fun m _ ih => List.cons (chainF m.2.1) ih) ms) sizes) (Nat.beq F msz)

@[expose] noncomputable def latG (n : Nat) (C : List Lvl) (d : Nat) (MG : List Nat)
    (MW : List (List (List Nat))) (k : Nat) (T : List (List Nat)) (L : Nat) (TG : List Nat)
    (lat : List (List Nat)) (ms : List MemG) (K : Nat) (lab : List Nat)
    (reps : List (Nat × Nat × List (List Nat))) (joins : List (Nat × Nat × Nat × List (List Nat)))
    (sizes : List Nat) (msz : Nat) : Bool :=
  andB (memsOKG TG lat ms) (andB (chainOK n C) (andB (grpT n C (chainF C) MG MW k T L d)
  (andB (allA ms (closedMG n d))
  (andB (Option.rec (motive := fun _ => Bool) false (fun Tm => coverG n C (chainF C) Tm K lab reps)
    (getO ms 0))
  (andB (repsG n TG ms reps)
  (andB (joinsG n ms joins)
  (andB (sizesG (chainF C) ms sizes msz)
    (tleC n C (chainF C) TG))))))))

@[expose] noncomputable def containsG (n d : Nat) (T : List Nat) (lat : List (List Nat))
    (ms : List MemG) (sizes : List Nat) (A : List Nat) (k s : Nat) : Bool :=
  andB (memsOKG T lat ms) (allN k fun j => orB (notB (Nat.beq (getK sizes j) s))
    (Option.rec (motive := fun _ => Bool) (allL A fun g => Nat.beq g (one n))
      (fun m => andB (closedMG n d m) (allL A (memG n m)))
      (getO ms j)))

@[expose] noncomputable def duK (n1 n2 a b : Nat) : Nat :=
  Nat.add a (Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Nat.add acc
    (Nat.shiftLeft (Nat.add n1 (img b j)) (Nat.mul 5 (Nat.add n1 j)))) n2)

@[expose] noncomputable def zipDU (n1 n2 : Nat) (A B : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun a _ ih B => List.rec (motive := fun _ => List Nat) []
      (fun b B' _ => List.cons (duK n1 n2 a b) (ih B')) B) A B

@[expose] noncomputable def fixHi (n1 n2 x : Nat) : Bool :=
  allN n2 fun j => Nat.beq (img x (Nat.add n1 j)) (Nat.add n1 j)

@[expose] noncomputable def kerOK (n1 : Nat) (K : List Nat) : Bool :=
  allL K fun x => andB (Nat.beq (mul n1 x x) (one n1))
    (allL K fun y => Nat.beq (mul n1 x y) (mul n1 y x))

@[expose] noncomputable def diagExtC (n1 n2 d : Nat) (A B : List Nat) (N M : Nat)
    (CA : List Lvl) (WA : List (List (List Nat))) (CB : List Lvl) (WB : List (List (List Nat)))
    (CD : List Lvl) (WD : List (List (List Nat))) : Bool :=
  CFSG.KC.LQT.S.allBs
  [closedMG n1 d (Prod.mk A (Prod.mk CA WA)), Nat.beq (chainF CA) N,
   closedMG n2 d (Prod.mk B (Prod.mk CB WB)), Nat.beq (chainF CB) M,
   closedMG (Nat.add n1 n2) d (Prod.mk (zipDU n1 n2 A B) (Prod.mk CD WD)), Nat.beq (chainF CD) N,
   Nat.beq (lenA A) (lenA B),
   kerOK n1 (CFSG.KC.LQT.PH.colAll (Nat.add n1 n2) CD (fun x => x) (fixHi n1 n2))]

end CFSG.KC.LQT.L

end
