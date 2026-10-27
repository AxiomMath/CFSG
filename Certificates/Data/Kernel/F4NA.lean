module

public import Certificates.Data.Kernel.F4Salt

public section

namespace CFSG.KC.F4NA

open CFSG.KC.F4Salt CFSG.KC.Loop

@[expose] noncomputable def l10 (X i : Nat) : Nat := Nat.land (Nat.shiftRight X (Nat.mul 10 i)) 1023

@[expose] noncomputable def l32 (X i : Nat) : Nat :=
  Nat.land (Nat.shiftRight X (Nat.mul 32 i)) 4294967295

@[expose] noncomputable def l2 (X i k : Nat) : Nat :=
  Nat.land (Nat.shiftRight X (Nat.add (Nat.mul 8 i) (Nat.mul 2 k))) 3

@[expose] noncomputable def bt (X i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight X i) 1) 1

@[expose] noncomputable def walkP (RT w L i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun i _ => i)
    (fun _ ih i w => ih (l10 RT (Nat.add (Nat.mul 6 i) (Nat.land w 7))) (Nat.shiftRight w 3))
    L i w

@[expose] noncomputable def mulI (RT PW i j : Nat) : Nat :=
  walkP RT (Nat.shiftRight (l32 PW j) 4) (Nat.land (l32 PW j) 15) i

@[expose] noncomputable def conjI (RT PW INV u x : Nat) : Nat :=
  mulI RT PW (mulI RT PW u x) (l10 INV u)

@[expose] noncomputable def commI (RT PW a b : Nat) : Bool :=
  Nat.beq (mulI RT PW a b) (mulI RT PW b a)

@[expose] noncomputable def cubeI (RT PW a : Nat) : Bool :=
  Nat.beq (mulI RT PW (mulI RT PW a a) a) 0

@[expose] def pk (w : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun v _ ih => Nat.add v (Nat.shiftLeft ih w)) l

@[expose] def allLt (b : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun v _ ih => Nat.blt v b && ih) l

@[expose] def lenR (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] def enc8 (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun v _ ih => Nat.add v (Nat.mul 8 ih)) l

@[expose] def pwOf (p : List Nat) : Nat := Nat.add (lenR p) (Nat.mul 16 (enc8 p))

@[expose] def bindB (w X : Nat) (l : List Nat) : Bool :=
  Nat.beq (pk w l) X && allLt (2 ^ w) l

@[expose] def pwB (PW : Nat) (ps : List (List Nat)) : Bool :=
  bindB 32 PW (ps.map pwOf) &&
    List.rec (motive := fun _ => Bool) true
      (fun p _ ih => Nat.blt (lenR p) 9 && allLt 8 p && ih) ps

@[expose] def gwB (ws : List (List Nat)) (gw : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → Bool)
    (fun gw => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) gw)
    (fun w _ ih gw => List.rec (motive := fun _ => Bool) false
      (fun p t _ => Nat.beq (enc8 w) p.1 && Nat.beq (lenR w) p.2 && allLt 8 w && ih t) gw) ws gw

@[expose] noncomputable def e3B (RT PW E3 : Nat) : Bool :=
  allBelow 729 12 fun i => Bool.rec (motive := fun _ => Bool) (!cubeI RT PW i) (cubeI RT PW i)
    (bt E3 i)

@[expose] noncomputable def cubeWtB (E3 WT : Nat) : Bool :=
  allBelow 729 12 fun i =>
    let w := Nat.beq (l2 WT i 0) 0 || Nat.beq (l2 WT i 1) 0 || Nat.beq (l2 WT i 2) 0
    Bool.rec (motive := fun _ => Bool) (!w) w (bt E3 i)

@[expose] noncomputable def wsum (wc c L : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun a _ => a)
    (fun _ ih a c => ih (Nat.add a (Nat.land (Nat.shiftRight wc (Nat.mul 2 (Nat.land c 7))) 3))
      (Nat.shiftRight c 3)) L 0 c

@[expose] noncomputable def wtB (PW WT wc k : Nat) : Bool :=
  allBelow 729 12 fun j =>
    Nat.beq (l2 WT j k) (Nat.mod (wsum wc (Nat.shiftRight (l32 PW j) 4) (Nat.land (l32 PW j) 15)) 3)

@[expose] noncomputable def homB (RT WT wc k : Nat) : Bool :=
  allBelow 4374 69 fun e =>
    Nat.beq (l2 WT (l10 RT e) k)
      (Nat.mod (Nat.add (l2 WT (Nat.div e 6) k)
        (Nat.land (Nat.shiftRight wc (Nat.mul 2 (Nat.mod e 6))) 3)) 3)

@[expose] noncomputable def centB (RT PW WT k z : Nat) : Bool :=
  allBelow 729 12 fun j =>
    Bool.rec (motive := fun _ => Bool) true (commI RT PW z j) (Nat.beq (l2 WT j k) 0)

@[expose] noncomputable def lS (MSP i : Nat) : Nat :=
  Nat.land (Nat.shiftRight MSP (Nat.mul 2832 i)) (Nat.sub (Nat.shiftLeft 1 2832) 1)

@[expose] noncomputable def edgeB (PW PAR MSP j : Nat) : Bool :=
  let p := l10 PAR j
  let q := l32 PW p
  let lp := Nat.land q 15
  let g := Nat.land (Nat.shiftRight (l32 PW j) (Nat.add 4 (Nat.mul 3 lp))) 7
  Nat.blt p j &&
    Nat.beq (l32 PW j)
      (Nat.add (Nat.succ lp) (Nat.shiftLeft (Nat.add (Nat.shiftRight q 4)
        (Nat.shiftLeft g (Nat.mul 3 lp))) 4)) &&
    eqS (mulS (lS MSP p) (lS MSP (Nat.succ g))) (lS MSP j)

@[expose] noncomputable def edgesB (PW PAR MSP lo n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k ih => bAnd(edgeB PW PAR MSP (Nat.add lo k), ih)) n

@[expose] noncomputable def genB (PW MSP : Nat) (g W L : Nat) : Bool :=
  Nat.beq (l32 PW (Nat.succ g)) (Nat.add 1 (Nat.mul 16 g)) && eqS (wordS W L) (lS MSP (Nat.succ g))

@[expose] noncomputable def trS (pos : List Nat) (A : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun p _ ih => xor (bt A (Nat.add 128 (Nat.mul 53 p))) ih) pos

@[expose] noncomputable def trB (pos : List Nat) (MSP TR lo n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k ih => bAnd(Bool.rec (motive := fun _ => Bool) (!trS pos (lS MSP (Nat.add lo k)))
      (trS pos (lS MSP (Nat.add lo k))) (bt TR (Nat.add lo k)), ih)) n

@[expose] noncomputable def conjsB (RT PW INV x : Nat) (us : List Nat) : Bool × Nat × Nat :=
  List.rec (motive := fun _ => Bool × Nat × Nat) (true, 0, 0)
    (fun u _ ih =>
      let c := conjI RT PW INV u x
      (ih.1 && Nat.blt u 729 && Nat.beq (Nat.land (Nat.shiftRight ih.2.2 c) 1) 0,
        Nat.succ ih.2.1, Nat.lor ih.2.2 (Nat.shiftLeft 1 c))) us

@[expose] noncomputable def witB (RT PW INV : Nat) (r : Nat × List Nat × Nat × Nat) : Bool :=
  let x := r.1
  let a := r.2.2.1
  let b := r.2.2.2
  let cs := conjsB RT PW INV x r.2.1
  Nat.blt x 729 && cs.1 && (Nat.beq cs.2.1 10 ||
    (Nat.beq cs.2.1 4 && Nat.blt a 729 && Nat.blt b 729 && cubeI RT PW a && cubeI RT PW b &&
      commI RT PW a x && commI RT PW b x && !commI RT PW a b))

@[expose] noncomputable def witsB (RT PW INV : Nat) (l : List (Nat × List Nat × Nat × Nat)) :
    Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ ih => bAnd(witB RT PW INV r, ih)) l

@[expose] noncomputable def cnt (p : Nat → Bool) : Nat :=
  sumBelow 729 12 fun i => nIf(p i, 1, 0)

@[expose] noncomputable def recMask (l : List (Nat × List Nat × Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun r _ ih => Nat.lor ih (Nat.shiftLeft 1 r.1)) l

@[expose] noncomputable def coverB (E3 WT M : Nat) : Bool :=
  allBelow 729 12 fun i =>
    Bool.rec (motive := fun _ => Bool) true (bt M i)
      (bt E3 i && !(Nat.beq (l2 WT i 0) 0 && Nat.beq (l2 WT i 3) 0))

end CFSG.KC.F4NA

end
