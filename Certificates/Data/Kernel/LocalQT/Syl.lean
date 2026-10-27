module

public import Certificates.Data.Kernel.LocalQT.Outer
public import Certificates.Data.Kernel.LocalQT.Tab2

public section

namespace CFSG.KC.LQT.Syl

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.W CFSG.KC.LQT.T2

@[expose] noncomputable def rlK (n cA cB : Nat) (rgw rwords : List (List Int)) : List Nat :=
  List.map (evalZK n (List.map (evalZK n [cA, cB]) rgw)) rwords

@[expose] noncomputable def sylBase (n a : Nat) (RL : List Nat) : Bool :=
  allBs [Nat.ble n 32, Nat.beq (lenL RL) (Nat.pow 2 a), distinctS RL, memL (one n) RL,
    allL RL fun x => Nat.beq (pow n x (Nat.pow 2 a)) (one n)]

@[expose] noncomputable def sylK (n a : Nat) (RL : List Nat) : Bool :=
  andB (sylBase n a RL) (allL RL fun x => allL RL fun y => memL (mul n x y) RL)

@[expose] noncomputable def sylGK (n a : Nat) (RL G : List Nat) : Bool :=
  andB (sylBase n a RL) (allL RL fun x => allL G fun g => memL (mul n x g) RL)

@[expose] noncomputable def invK (n : Nat) (RL : List Nat) : List Nat :=
  filtL RL fun x => andB (notB (Nat.beq x (one n))) (Nat.beq (mul n x x) (one n))

@[expose] noncomputable def pairK (n : Nat) (I : List Nat) : List (Nat × Nat) :=
  List.flatten (List.map (fun x => List.rec (motive := fun _ => List (Nat × Nat)) []
    (fun y _ ih => Bool.rec (motive := fun _ => List (Nat × Nat)) ih (List.cons (x, y) ih)
      (andB (notB (Nat.beq x y)) (comm n x y))) I) I)

@[expose] noncomputable def eqL (l : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun x _ ih m => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => andB (Nat.beq x y) (ih ys)) m) l

@[expose] noncomputable def dedupLL (Ls : List (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat) → List (List Nat)) (fun acc => acc)
    (fun L _ ih acc => ih (Bool.rec (motive := fun _ => List (List Nat)) (List.cons L acc) acc
      (List.rec (motive := fun _ => Bool) false (fun M _ ih2 => orB (eqL L M) ih2) acc))) Ls []

@[expose] noncomputable def extK (n : Nat) (I : List Nat) (Es : List (List Nat)) :
    List (List Nat) :=
  dedupLL (List.flatten (List.map (fun E => List.flatten (List.map (fun x =>
    Bool.rec (motive := fun _ => List (List Nat)) []
      [sortK (List.append E (List.map (mul n x) E))]
      (andB (allL E fun e => comm n x e) (notB (memL x E)))) I)) Es))

@[expose] noncomputable def rankK (n : Nat) (I : List Nat) (k : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false)
    (Nat.rec (motive := fun _ => List (List Nat)) [[one n]] (fun _ ih => extK n I ih) k)

@[expose] noncomputable def witK (n : Nat) (ts cj w : List Nat) (p : Nat) : Bool :=
  letB (evalWK n (List.append ts (List.flatten (List.map (fun c => List.map (conj n c) ts) cj))) w)
    fun z => andB (Nat.beq (pow n z p) (one n)) (notB (Nat.beq z (one n)))

@[expose] noncomputable def getK {α : Type} (l : List α) (i : Nat) (d : α) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun x _ ih j => Nat.rec (motive := fun _ => α) x (fun j' _ => ih j') j) l i

@[expose] noncomputable def lenK {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def g1okK (n cA cB : Nat) (RL : List Nat)
    (G1 : List (Nat × List (List Int) × List Nat)) (p : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => andB (andB (Nat.beq (lenK e.2.1) 2)
    (witK n [getK RL e.1 (one n)] (List.map (evalZK n [cA, cB]) e.2.1) e.2.2 p)) ih) G1

@[expose] noncomputable def g2okK (n cA cB : Nat) (RL : List Nat)
    (G2 : List (Nat × Nat × List (List Int) × List Nat)) (p : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => andB (andB (Nat.beq (lenK e.2.2.1) 1)
    (witK n [getK RL e.1 (one n), getK RL e.2.1 (one n)] (List.map (evalZK n [cA, cB]) e.2.2.1)
      e.2.2.2 p)) ih) G2

@[expose] noncomputable def zipAll {α : Type} (l : List α) (h : List (Nat × Nat))
    (f : α → Nat × Nat → Bool) : Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → Bool)
    (fun h => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) h)
    (fun x _ ih h => List.rec (motive := fun _ => Bool) false
      (fun q qs _ => andB (f x q) (ih qs)) h) l h

@[expose] noncomputable def g1covK (n : Nat) (RL : List Nat)
    (G1 : List (Nat × List (List Int) × List Nat)) (hs : List (Nat × Nat)) : Bool :=
  zipAll (invK n RL) hs fun x q => andB (Nat.blt q.1 (lenK G1)) (andB (Nat.blt q.2 (lenL RL))
    (Nat.beq (conj n (getK RL q.2 (one n)) x) (getK RL (getK G1 q.1 (0, [], [])).1 (one n))))

@[expose] noncomputable def g2covK (n : Nat) (RL : List Nat)
    (G2 : List (Nat × Nat × List (List Int) × List Nat)) (hs : List (Nat × Nat)) : Bool :=
  zipAll (pairK n (invK n RL)) hs fun x q => andB (Nat.blt q.1 (lenK G2))
    (andB (Nat.blt q.2 (lenL RL))
    (andB (Nat.beq (conj n (getK RL q.2 (one n)) x.1) (getK RL (getK G2 q.1 (0, 0, [], [])).1 (one n)))
      (Nat.beq (conj n (getK RL q.2 (one n)) x.2)
        (getK RL (getK G2 q.1 (0, 0, [], [])).2.1 (one n)))))

end CFSG.KC.LQT.Syl

end
