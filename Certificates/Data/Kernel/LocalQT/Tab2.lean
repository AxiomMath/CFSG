module

public import Certificates.Data.Kernel.LocalQT.Small

public section

namespace CFSG.KC.LQT.T2

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S

@[expose] noncomputable def codeT (t : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.add x (Nat.mul 32 ih)) t

@[expose] noncomputable def tabOK (n : Nat) (t : List Nat) : Bool :=
  andB (Nat.beq (lenL t) n) (andB (allL t fun x => Nat.blt x n) (permK n (codeT t)))

@[expose] noncomputable def mkS (ok sec dig first cur : Nat) : Nat :=
  Nat.add (Nat.add ok (Nat.add (Nat.mul 2 sec) (Nat.mul 4 dig)))
    (Nat.add (Nat.mul 8 first) (Nat.mul 8388608 cur))

@[expose] noncomputable def bitS (s i : Nat) : Nat := Nat.mod (Nat.div s (Nat.pow 2 i)) 2

@[expose] noncomputable def fstS (s : Nat) : Nat := Nat.mod (Nat.div s 8) 1048576

@[expose] noncomputable def curS (s : Nat) : Nat := Nat.div s 8388608

@[expose] noncomputable def stepS (c s : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) 0
        (Bool.rec (motive := fun _ => Nat) 0 (mkS (bitS s 0) 0 0 0 0)
          (andB (Nat.beq (bitS s 1) 1) (Nat.beq (bitS s 2) 1)))
        (Nat.beq c 32))
      (Bool.rec (motive := fun _ => Nat) 0 (mkS (bitS s 0) 1 0 (curS s) 0)
        (andB (Nat.beq (bitS s 1) 0) (andB (Nat.beq (bitS s 2) 1) (Nat.blt (curS s) 1048576))))
      (Nat.beq c 44))
    (mkS (bitS s 0) (bitS s 1) 1 (fstS s) (Nat.add (Nat.mul 10 (curS s)) (Nat.sub c 48)))
    (andB (Nat.ble 48 c) (Nat.ble c 57))

@[expose] noncomputable def letPN (y : Nat) (k : Nat → Nat × List (Nat × Nat)) :
    Nat × List (Nat × Nat) :=
  Nat.rec (motive := fun _ => Nat × List (Nat × Nat)) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def runP (cs : List Char) : Nat × List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat) → Nat × List (Nat × Nat))
    (fun s acc => Prod.mk s acc)
    (fun c _ ih s acc => letPN (stepS (Char.toNat c) s) fun s' =>
      ih s' (Bool.rec (motive := fun _ => List (Nat × Nat)) acc
        (List.cons (Prod.mk (fstS s) (curS s)) acc)
        (andB (Nat.beq (Char.toNat c) 32) (Nat.beq (bitS s' 0) 1))))
    cs (mkS 1 0 0 0 0) []

@[expose] noncomputable def parseK (cs : List Char) : Option (List (Nat × Nat)) :=
  Bool.rec (motive := fun _ => Option (List (Nat × Nat))) none
    (some (List.reverse (List.cons (Prod.mk (fstS (runP cs).1) (curS (runP cs).1)) (runP cs).2)))
    (andB (Nat.beq (bitS (runP cs).1 0) 1)
      (andB (Nat.beq (bitS (runP cs).1 1) 1) (Nat.beq (bitS (runP cs).1 2) 1)))

@[expose] noncomputable def allT {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) l

@[expose] noncomputable def getDK (l : List Nat) (i d : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => d)
    (fun x _ ih j => Bool.rec (motive := fun _ => Nat) (ih (Nat.sub j 1)) x (Nat.beq j 0)) l i

@[expose] noncomputable def bfsT (op : Nat → Nat → Nat) (d : Nat) (gens : List Nat) (start : Nat)
    (par : List (Nat × Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun pk _ ih acc => ih (List.append acc [op (getDK acc pk.1 start) (getDK gens pk.2 d)]))
    par [start]

@[expose] noncomputable def letL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def normQ (F R : List Nat) (k : List Nat → List Nat → List Nat) :
    List Nat :=
  List.rec (motive := fun _ => List Nat) (k (List.reverse R) []) (fun x xs _ => k (List.cons x xs) R) F

@[expose] noncomputable def dropQ (m : Nat) (k : List Nat → List Nat → List Nat) :
    List Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat → List Nat) (fun F R => normQ F R k)
    (fun _ ih F R => normQ F R fun F₁ R₁ => ih (List.tail F₁) R₁) m

@[expose] noncomputable def headK (l : List Nat) (d : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) d (fun x _ _ => x) l

@[expose] noncomputable def monoK (par : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun pk _ ih i c => letB i fun i' => andB (Nat.ble c pk.1) (andB (Nat.ble pk.1 i')
      (ih (Nat.succ i') pk.1))) par 0 0

@[expose] noncomputable def bfsQ (op : Nat → Nat → Nat) (d : Nat) (gens : List Nat) (start : Nat)
    (par : List (Nat × Nat)) : List Nat :=
  List.reverse (List.rec (motive := fun _ => List Nat → Nat → List Nat → List Nat → List Nat)
    (fun _ _ _ O => O)
    (fun pk _ ih F c R O => dropQ (Nat.sub pk.1 c) (fun F₁ R₁ =>
      letL (op (headK F₁ start) (getDK gens pk.2 d)) fun y =>
        ih F₁ pk.1 (List.cons y R₁) (List.cons y O)) F R)
    par [start] 0 [] [start])

@[expose] noncomputable def spanLt (x : Nat) (ys : List Nat) (k : List Nat → List Nat → List Nat) :
    List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => k (List.reverse acc) [])
    (fun y ys' ih acc => Bool.rec (motive := fun _ => List Nat) (k (List.reverse acc) (List.cons y ys'))
      (ih (List.cons y acc)) (Nat.blt y x)) ys

@[expose] noncomputable def mergeK (xs : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun ys => ys)
    (fun x _ ih ys => spanLt x ys (fun p r => List.append p (List.cons x (ih r))) []) xs

@[expose] noncomputable def passK (rs : List (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => Option (List Nat) → List (List Nat))
    (fun o => Option.rec (motive := fun _ => List (List Nat)) [] (fun a => [a]) o)
    (fun r _ ih o => Option.rec (motive := fun _ => List (List Nat)) (ih (some r))
      (fun a => List.cons (mergeK a r) (ih none)) o) rs none

@[expose] noncomputable def sortK (l : List Nat) : List Nat :=
  List.flatten (Nat.rec (motive := fun _ => List (List Nat)) (List.map (fun x => [x]) l)
    (fun _ ih => passK ih) 13)

@[expose] noncomputable def sincK (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Option Nat → Bool) (fun _ => true)
    (fun x _ ih o => andB (Option.rec (motive := fun _ => Bool) true (fun y => Nat.blt y x) o)
      (ih (some x))) l none

@[expose] noncomputable def distinctS (l : List Nat) : Bool := sincK (sortK l)

@[expose] noncomputable def spanK (n : Nat) (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [one n]
    (fun e _ ih => List.append ih (List.rec (motive := fun _ => List Nat) []
      (fun x _ ih2 => List.cons (mul n e x) ih2) ih)) l

@[expose] noncomputable def letK (n A B l : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (inv n B) (inv n A) (Nat.beq l 2)) B (Nat.beq l 1))
    A (Nat.beq l 0)

@[expose] noncomputable def wordK (n A B : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => ih (mul n acc (letK n A B l))) w (one n)

@[expose] noncomputable def closedT (n : Nat) (L : List Nat) : Bool :=
  andB (memL (one n) L) (andB (allL L fun s => allL L fun t => memL (mul n s t) L)
    (allL L fun t => memL (inv n t) L))

@[expose] noncomputable def eokT (n : Nat) (Pl E : List Nat) : Bool :=
  allBs [distinctL E, Nat.beq (lenL E) 16, allL E fun t => memL t Pl,
    allL E (fun s => allL E fun t => comm n s t), allL E fun t => Nat.beq (mul n t t) (one n)]

@[expose] noncomputable def selfCentT (n : Nat) (Hl E : List Nat) : Bool :=
  allL Hl fun h => impB (allL E fun e => comm n h e) (memL h E)

@[expose] noncomputable def witT (n g : Nat) (E₁ E₂ : List Nat) : Bool :=
  andB (allL E₂ fun e => memL (conj n g e) E₂) (anyL E₁ fun e => notB (memL (conj n g e) E₁))

@[expose] noncomputable def allTail (l : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x xs ih => andB (f x xs) ih) l

@[expose] noncomputable def classT (n : Nat) (Pl Ea Eb : List Nat) : Bool :=
  allTail (filtL Pl fun t => andB (notB (Nat.beq t (one n))) (Nat.beq (mul n t t) (one n)))
    fun t1 r1 => allTail r1 fun t2 r2 => impB (comm n t1 t2) (allTail r2 fun t3 r3 =>
      impB (andB (comm n t1 t3) (comm n t2 t3)) (allTail r3 fun t4 _ =>
        impB (andB (comm n t1 t4) (andB (comm n t2 t4) (comm n t3 t4)))
          (orB (Nat.blt (lenL (dedupL (spanK n [t1, t2, t3, t4]))) 16)
            (orB (allL (spanK n [t1, t2, t3, t4]) fun s => memL s Ea)
              (allL (spanK n [t1, t2, t3, t4]) fun s => memL s Eb)))))

@[expose] noncomputable def checkK (n : Nat) (ta tb : List Nat) (order : Nat) (clS : List Char)
    (hGensW : List (List Nat)) (hS : List Char) (pGensW : List (List Nat)) (pS : List Char)
    (eaGens ebGens : List (List Nat)) (gaW gbW : List Nat) : Bool :=
  Option.rec (motive := fun _ => Bool) false (fun clPar =>
  Option.rec (motive := fun _ => Bool) false (fun hPar =>
  Option.rec (motive := fun _ => Bool) false (fun pPar =>
  letB (codeT ta) fun A => letB (codeT tb) fun B =>
  letI L := [A, B, inv n A, inv n B]
  letI cl := bfsQ (fun x g => mul n (mul n g x) (inv n g)) (one n) L A clPar
  letI Hl := bfsQ (mul n) (one n) (List.map (wordK n A B) hGensW) (one n) hPar
  letI Pl := bfsQ (mul n) (one n) (List.map (wordK n A B) pGensW) (one n) pPar
  letI Ea := spanK n (List.map codeT eaGens)
  letI Eb := spanK n (List.map codeT ebGens)
  allBs
  [monoK clPar, monoK hPar, monoK pPar,
   tabOK n ta, tabOK n tb, allT eaGens (tabOK n), allT ebGens (tabOK n),
   distinctS cl, distinctS Hl, Nat.beq (Nat.mul (lenL cl) (lenL Hl)) order,
   allL Hl (fun h => comm n h A),
   distinctL Pl, Nat.beq (lenL Pl) 128, Nat.beq (Nat.mod (Nat.div order 128) 2) 1,
   closedT n Pl, closedT n Ea, closedT n Eb, eokT n Pl Ea, eokT n Pl Eb,
   memL A Ea, memL A Eb, anyL Ea (fun t => notB (memL t Eb)),
   selfCentT n Hl Ea, selfCentT n Hl Eb,
   witT n (wordK n A B gaW) Ea Eb, witT n (wordK n A B gbW) Eb Ea,
   classT n Pl Ea Eb])
  (parseK pS)) (parseK hS)) (parseK clS)

end CFSG.KC.LQT.T2

end
