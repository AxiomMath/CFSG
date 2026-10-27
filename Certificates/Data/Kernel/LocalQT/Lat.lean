module

public import Certificates.Data.Kernel.LocalQT.Word
public import Certificates.Data.Kernel.LocalQT.Small

public section

namespace CFSG.KC.LQT.L

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.W

inductive NT where
  | lf : NT
  | nd : NT → Nat → NT → NT

@[expose] noncomputable def hashK (x : Nat) : Nat :=
  Nat.land (Nat.mul x 11400714819323198485) 18446744073709551615

@[expose] noncomputable def ltK (x y : Nat) : Bool :=
  letB (hashK x) fun hx => letB (hashK y) fun hy =>
    orB (Nat.blt hx hy) (andB (Nat.beq hx hy) (Nat.blt x y))

@[expose] noncomputable def memT (t : NT) (x : Nat) : Bool :=
  NT.rec (motive := fun _ => Bool) false
    (fun _ k _ ihl ihr => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) ihr ihl (ltK x k)) true (Nat.beq x k)) t

@[expose] noncomputable def insT (t : NT) (x : Nat) : NT :=
  NT.rec (motive := fun _ => NT) (NT.nd NT.lf x NT.lf)
    (fun l k r ihl ihr => Bool.rec (motive := fun _ => NT)
      (Bool.rec (motive := fun _ => NT) (NT.nd l k ihr) (NT.nd ihl k r) (ltK x k))
      (NT.nd l k r) (Nat.beq x k)) t

structure SetK where
  t : NT
  size : Nat
  elems : List Nat

@[expose] noncomputable def allA {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) l

@[expose] noncomputable def anyA {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => orB (f x) ih) l

@[expose] noncomputable def lenA {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def getO {α : Type} (l : List α) (i : Nat) : Option α :=
  List.rec (motive := fun _ => Nat → Option α) (fun _ => none)
    (fun x _ ih j => Bool.rec (motive := fun _ => Option α) (ih (Nat.sub j 1)) (some x)
      (Nat.beq j 0)) l i

@[expose] noncomputable def addK (S : SetK × List Nat) (y : Nat) : SetK × List Nat :=
  Bool.rec (motive := fun _ => SetK × List Nat)
    (Prod.mk (SetK.mk (insT S.1.t y) (Nat.succ S.1.size) (List.cons y S.1.elems)) (List.cons y S.2))
    S (memT S.1.t y)

@[expose] noncomputable def roundG (mf : Nat → Nat → Nat) (G : List Nat) (S : SetK)
    (F : List Nat) : SetK × List Nat :=
  List.rec (motive := fun _ => SetK × List Nat → SetK × List Nat) (fun st => st)
    (fun x _ ih st => ih (List.rec (motive := fun _ => SetK × List Nat → SetK × List Nat)
      (fun st => st) (fun g _ ih2 st => ih2 (addK st (mf x g))) G st)) F (Prod.mk S [])

@[expose] noncomputable def bfsG (mf : Nat → Nat → Nat) (o : Nat) (G : List Nat) (d : Nat) :
    SetK :=
  (Nat.rec (motive := fun _ => SetK × List Nat)
    (Prod.mk (SetK.mk (NT.nd NT.lf o NT.lf) 1 [o]) [o])
    (fun _ st => roundG mf G st.1 st.2) d).1

@[expose] noncomputable def closedG (mf : Nat → Nat → Nat) (o : Nat) (G : List Nat) (S : SetK) :
    Bool :=
  andB (memT S.t o) (allL S.elems fun x => allL G fun g => memT S.t (mf x g))

@[expose] noncomputable def bfsK (n : Nat) (G : List Nat) (d : Nat) : SetK :=
  bfsG (mul n) (one n) G d

@[expose] noncomputable def closedK (n : Nat) (G : List Nat) (S : SetK) : Bool :=
  closedG (mul n) (one n) G S

@[expose] noncomputable def eqK (n : Nat) (EB : SetK) (A B : List Nat) (ws : List (List Nat)) :
    Bool :=
  andB (allL A fun g => memT EB.t g) (andB (Nat.beq (lenA ws) (lenA B))
    (List.rec (motive := fun _ => List (List Nat) → Bool) (fun _ => true)
      (fun b _ ih ws => List.rec (motive := fun _ => Bool) true
        (fun w ws' _ => andB (Nat.beq (evalWK n A w) b) (ih ws')) ws) B ws))

@[expose] noncomputable def eqL (l m : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun x _ ih m => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => andB (Nat.beq x y) (ih ys)) m) l m

@[expose] noncomputable def membersK (n d : Nat) (T : List Nat) (lat : List (List Nat)) :
    List (List Nat × SetK) :=
  List.rec (motive := fun _ => List (List Nat × SetK)) []
    (fun L _ ih => List.cons (Prod.mk L (bfsK n L d)) ih) (List.cons T lat)

@[expose] noncomputable def dcK (n : Nat) (ET : SetK) (reps : List (Nat × Nat × List (List Nat))) :
    NT :=
  List.rec (motive := fun _ => NT) NT.lf
    (fun r _ ih => List.rec (motive := fun _ => NT) ih
      (fun e _ ih2 => List.rec (motive := fun _ => NT) ih2
        (fun f _ ih3 => insT ih3 (mul n (mul n e r.1) f)) ET.elems) ET.elems) reps

@[expose] noncomputable def repsK (n : Nat) (T : List Nat) (mem : List (List Nat × SetK))
    (reps : List (Nat × Nat × List (List Nat))) : Bool :=
  allA reps fun r => Option.rec (motive := fun _ => Bool) false
    (fun p => eqK n p.2 (List.append T [r.1]) p.1 r.2.2) (getO mem r.2.1)

@[expose] noncomputable def joinsK (n : Nat) (mem : List (List Nat × SetK))
    (joins : List (Nat × Nat × Nat × List (List Nat))) : Bool :=
  andB (allN (lenA mem) fun a => allN (lenA mem) fun b =>
      anyA joins fun j => andB (Nat.beq j.1 a) (Nat.beq j.2.1 b))
    (allA joins fun j =>
      Option.rec (motive := fun _ => Bool) false (fun pa =>
      Option.rec (motive := fun _ => Bool) false (fun pb =>
      Option.rec (motive := fun _ => Bool) false (fun pc =>
        eqK n pc.2 (List.append pa.1 pb.1) pc.1 j.2.2.2)
        (getO mem j.2.2.1)) (getO mem j.2.1)) (getO mem j.1))

@[expose] noncomputable def closedOKK (n d : Nat) (MG T : List Nat) (lat : List (List Nat)) :
    Bool :=
  andB (closedK n MG (bfsK n MG d)) (allA (membersK n d T lat) fun p => closedK n p.1 p.2)

@[expose] noncomputable def coverK (n d : Nat) (MG T : List Nat)
    (reps : List (Nat × Nat × List (List Nat))) : Bool :=
  allL (bfsK n MG d).elems (memT (dcK n (bfsK n T d) reps))

@[expose] noncomputable def sizesK (n d : Nat) (MG T : List Nat) (lat : List (List Nat))
    (sizes : List Nat) (ms : Nat) : Bool :=
  andB (eqL (List.rec (motive := fun _ => List Nat) []
      (fun p _ ih => List.cons p.2.size ih) (membersK n d T lat)) sizes)
    (Nat.beq (bfsK n MG d).size ms)

@[expose] noncomputable def tleK (n d : Nat) (MG T : List Nat) : Bool :=
  allL T fun g => memT (bfsK n MG d).t g

@[expose] noncomputable def latK (n d : Nat) (MG T : List Nat) (lat : List (List Nat))
    (reps : List (Nat × Nat × List (List Nat))) (joins : List (Nat × Nat × Nat × List (List Nat)))
    (sizes : List Nat) (ms : Nat) : Bool :=
  andB (closedOKK n d MG T lat) (andB (coverK n d MG T reps)
  (andB (repsK n T (membersK n d T lat) reps) (andB (joinsK n (membersK n d T lat) joins)
  (andB (sizesK n d MG T lat sizes ms) (tleK n d MG T)))))

@[expose] noncomputable def ctK (n d : Nat) (H N : List Nat) (e : Nat) : Bool :=
  CFSG.KC.LQT.S.allBs
  [closedK n H (bfsK n H d), closedK n N (bfsK n N d),
   allL N fun x => memT (bfsK n H d).t x,
   allL (bfsK n H d).elems (fun r => allL N fun x =>
     anyL (bfsK n N d).elems fun x' => Nat.beq (mul n r x) (mul n x' r)),
   allL (bfsK n H d).elems (fun r =>
     orB (notB (allL N fun x => Nat.beq (mul n r x) (mul n x r))) (memT (bfsK n N d).t r)),
   Nat.beq (bfsK n N d).size (Nat.pow 2 e)]

@[expose] noncomputable def memberK (n d : Nat) (T : List Nat) (lat : List (List Nat)) (ms : Nat)
    (cts : List (Nat × List Nat × List Nat × Nat)) : Bool :=
  allA (List.cons T lat) fun L => orB (Nat.beq (bfsK n L d).size ms)
    (anyA cts fun c => andB (eqL c.2.1 L) (ctK n c.1 c.2.1 c.2.2.1 c.2.2.2))

@[expose] noncomputable def setEqK (a b : SetK) : Bool :=
  andB (Nat.beq a.size b.size) (andB (allL a.elems (memT b.t)) (allL b.elems (memT a.t)))

@[expose] noncomputable def isLatK (n d : Nat) (G : List Nat) (Ls : List (List Nat)) : Bool :=
  andB (closedK n G (bfsK n G d)) (anyA Ls fun Z => setEqK (bfsK n G d) (bfsK n Z d))

@[expose] noncomputable def bitK (m i : Nat) : Nat := Nat.land (Nat.shiftRight m i) 1

@[expose] noncomputable def entK (m r c : Nat) : Nat := bitK m (Nat.add (Nat.mul 3 r) c)

@[expose] noncomputable def detK2 (m : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.add
    (Nat.mul (entK m 0 0)
      (Nat.add (Nat.mul (entK m 1 1) (entK m 2 2)) (Nat.mul (entK m 1 2) (entK m 2 1))))
    (Nat.mul (entK m 0 1)
      (Nat.add (Nat.mul (entK m 1 0) (entK m 2 2)) (Nat.mul (entK m 1 2) (entK m 2 0)))))
    (Nat.mul (entK m 0 2)
      (Nat.add (Nat.mul (entK m 1 0) (entK m 2 1)) (Nat.mul (entK m 1 1) (entK m 2 0)))))
    2

@[expose] noncomputable def mvK (m v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun r acc => Nat.add acc (Nat.mul (Nat.shiftLeft 1 r)
    (Nat.mod (Nat.rec (motive := fun _ => Nat) 0
      (fun c s => Nat.add s (Nat.mul (entK m r c) (bitK v c))) 3) 2))) 3

@[expose] noncomputable def idxK (V : List Nat) (w : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 6 (fun k acc => Bool.rec (motive := fun _ => Nat) acc
    (Nat.sub 5 k) (Nat.beq (CFSG.KC.LQT.S.getK V (Nat.sub 5 k)) w)) 6

@[expose] noncomputable def rhoK (V : List Nat) (m : Nat) : Nat :=
  ofFn 7 fun i => idxK V (mvK m (CFSG.KC.LQT.S.getK V i))

@[expose] noncomputable def rhoInK (V G : List Nat) (d : Nat) : Bool :=
  allN 512 fun m => impB (Nat.beq (detK2 m) 1) (memT (bfsK 7 G d).t (rhoK V m))

@[expose] noncomputable def pk (n1 a b : Nat) : Nat := Nat.add a (Nat.shiftLeft b (Nat.mul 5 n1))

@[expose] noncomputable def pairMul (n1 n2 p q : Nat) : Nat :=
  CFSG.KC.Loop.strictN (Nat.sub (Nat.shiftLeft 1 (Nat.mul 5 n1)) 1) fun m =>
    pk n1 (mul n1 (Nat.land p m) (Nat.land q m))
      (mul n2 (Nat.shiftRight p (Nat.mul 5 n1)) (Nat.shiftRight q (Nat.mul 5 n1)))

@[expose] noncomputable def zipK (n1 : Nat) (A B : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun a _ ih B => List.rec (motive := fun _ => List Nat) []
      (fun b B' _ => List.cons (pk n1 a b) (ih B')) B) A B

@[expose] noncomputable def diagK (n1 n2 d : Nat) (A B : List Nat) (N : Nat) : Bool :=
  CFSG.KC.LQT.S.allBs
  [closedK n1 A (bfsK n1 A d), Nat.beq (bfsK n1 A d).size N,
   closedK n2 B (bfsK n2 B d), Nat.beq (bfsK n2 B d).size N,
   closedG (pairMul n1 n2) (pk n1 (one n1) (one n2)) (zipK n1 A B)
     (bfsG (pairMul n1 n2) (pk n1 (one n1) (one n2)) (zipK n1 A B) d),
   Nat.beq (bfsG (pairMul n1 n2) (pk n1 (one n1) (one n2)) (zipK n1 A B) d).size N,
   Nat.beq (lenA A) (lenA B)]

end CFSG.KC.LQT.L

end
