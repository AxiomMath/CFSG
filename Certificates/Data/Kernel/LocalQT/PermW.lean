module

public import Certificates.Data.Kernel.LocalQT.PairsH

public section

namespace CFSG.KC.LQT.PW

open CFSG.KC.Ord

@[expose] noncomputable def imgW (w s i : Nat) : Nat :=
  Nat.land (Nat.shiftRight s (Nat.mul w i)) (Nat.sub (Nat.shiftLeft 1 w) 1)

@[expose] noncomputable def ofFnW (n w : Nat) (g : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (g i) (Nat.mul w i))) n

@[expose] noncomputable def mulW (n w s t : Nat) : Nat := ofFnW n w fun i => imgW w s (imgW w t i)

@[expose] noncomputable def invW (n w s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft i (Nat.mul w (imgW w s i)))) n

@[expose] noncomputable def oneW (n w : Nat) : Nat := ofFnW n w fun i => i

@[expose] noncomputable def arrCodeW (w : Nat) (t : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih k => Nat.lor (Nat.shiftLeft x (Nat.mul w k)) (ih (Nat.succ k))) t 0

@[expose] noncomputable def encW (n w x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.add (Nat.mul acc n) (imgW w x (Nat.sub (Nat.sub n 1) k))) n

@[expose] noncomputable def hkW (n w x : Nat) : Nat := Nat.mod (encW n w x) CFSG.KC.LQT.PH.hP

@[expose] noncomputable def conjW (n w g x : Nat) : Nat := mulW n w (mulW n w g x) (invW n w g)

@[expose] noncomputable def conjIW (n w g x : Nat) : Nat := mulW n w (mulW n w (invW n w g) x) g

@[expose] noncomputable def commW (n w x y : Nat) : Bool := Nat.beq (mulW n w x y) (mulW n w y x)

@[expose] noncomputable def powW (n w s k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (oneW n w) (fun _ acc => mulW n w acc s) k

@[expose] noncomputable def sqW (n w x e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun _ ih y => CFSG.KC.LQT.Syl.letN (mulW n w y y) ih) e x

@[expose] noncomputable def genW (n w : Nat) (G : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => oneW n w)
    (fun x _ ih j => Bool.rec (motive := fun _ => Nat) (ih (Nat.sub j 1)) x (Nat.beq j 0)) G i

@[expose] noncomputable def letW (n w : Nat) (G : List Nat) (z : Int) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun m => Nat.rec (motive := fun _ => Nat) (invW n w (genW n w G 0))
      (fun k _ => genW n w G k) m)
    (fun m => invW n w (genW n w G m)) z

@[expose] noncomputable def evalZW (n w : Nat) (G : List Nat) (ws : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) (oneW n w) (fun z _ ih => mulW n w (letW n w G z) ih) ws

@[expose] noncomputable def imgMaskW (n w g m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Bool.rec (motive := fun _ => Nat) acc (Nat.lor acc (Nat.shiftLeft 1 (imgW w g i)))
      (Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1)) n

@[expose] noncomputable def fixMaskW (n w : Nat) (L : List Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Bool.rec (motive := fun _ => Nat) acc (Nat.lor acc (Nat.shiftLeft 1 i))
      (CFSG.KC.LQT.P.allL L fun a => Nat.beq (imgW w a i) i)) n

@[expose] noncomputable def zipN (l h : List Nat) (f : Nat → Nat → Bool) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun h => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) h)
    (fun x _ ih h => List.rec (motive := fun _ => Bool) false
      (fun e h' _ => andB (f x e) (ih h')) h) l h

@[expose] noncomputable def nilK (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l

@[expose] noncomputable def grpE (G P : List Nat) : List Nat :=
  CFSG.KC.LQT.T2.bfsQ (fun x g => mulW 315 9 g x) (oneW 315 9) G (oneW 315 9)
    (CFSG.KC.LQT.Syl.pairUpK P)

@[expose] noncomputable def closedG (g : Nat) (E : List Nat) : Bool :=
  nilK (CFSG.KC.LQT.Syl.diffS (CFSG.KC.LQT.Syl.dedupS (CFSG.KC.LQT.Syl.sortN
    (List.map (fun x => mulW 315 9 g x) E))) (CFSG.KC.LQT.Syl.sortN E))

@[expose] noncomputable def closedE (G E : List Nat) : Bool :=
  CFSG.KC.LQT.P.allL G fun g => closedG g E

@[expose] noncomputable def closedS (g : Nat) (E : List Nat) (s k : Nat) : Bool :=
  nilK (CFSG.KC.LQT.Syl.diffS (CFSG.KC.LQT.Syl.dedupS (CFSG.KC.LQT.Syl.sortN
    (List.map (fun x => mulW 315 9 g x) (List.take k (List.drop s E))))) (CFSG.KC.LQT.Syl.sortN E))

@[expose] noncomputable def depthOK (G P : List Nat) (d : Nat) : Bool :=
  CFSG.KC.LQT.P.allL (CFSG.KC.LQT.T2.bfsQ (fun x _ => Nat.succ x) 0 G 0
    (CFSG.KC.LQT.Syl.pairUpK P)) fun k => Nat.ble k d

@[expose] noncomputable def orbE (G : List Nat) (M : Nat) (P : List Nat) : List Nat :=
  CFSG.KC.LQT.T2.bfsQ (fun m g => imgMaskW 315 9 g m) 0 G M (CFSG.KC.LQT.Syl.pairUpK P)

@[expose] noncomputable def closedM (G E : List Nat) : Bool :=
  nilK (CFSG.KC.LQT.Syl.diffS (CFSG.KC.LQT.Syl.dedupS (CFSG.KC.LQT.Syl.sortN (List.flatten
    (List.map (fun m => List.map (fun g => imgMaskW 315 9 g m) G) E)))) (CFSG.KC.LQT.Syl.sortN E))

@[expose] noncomputable def sliceK (l : List Nat) (s k : Nat) : List Nat :=
  List.take k (List.drop s l)

end CFSG.KC.LQT.PW

end
