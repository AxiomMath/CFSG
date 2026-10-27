module

public import Certificates.Data.Kernel.Misc.G24

public section

namespace CFSG.KC.L34Q

open CFSG.KC.Misc CFSG.KC.Misc.G24

@[expose] noncomputable def MT : Nat := 0b10011100011110001110010000000000

@[expose] noncomputable def fm (x y : Nat) : Nat :=
  Nat.land (Nat.shiftRight MT (Nat.mul 2 (Nat.add (Nat.mul 4 x) y))) 3

@[expose] noncomputable def actN (a a' b1 b b2 s t v : Nat) : Nat :=
  letN (Nat.land v 3) fun x00 => letN (Nat.land (Nat.shiftRight v 2) 3) fun x01 =>
  letN (Nat.land (Nat.shiftRight v 4) 3) fun x10 => letN (Nat.shiftRight v 6) fun x11 =>
  letN (Bool.rec (motive := fun _ => Nat) x00 (fm x00 x00) (Nat.beq t 1)) fun y00 =>
  letN (Bool.rec (motive := fun _ => Nat) x01 (fm x01 x01) (Nat.beq t 1)) fun z01 =>
  letN (Bool.rec (motive := fun _ => Nat) x10 (fm x10 x10) (Nat.beq t 1)) fun z10 =>
  letN (Bool.rec (motive := fun _ => Nat) x11 (fm x11 x11) (Nat.beq t 1)) fun y11 =>
  letN (Bool.rec (motive := fun _ => Nat) z01 z10 (Nat.beq s 1)) fun y01 =>
  letN (Bool.rec (motive := fun _ => Nat) z10 z01 (Nat.beq s 1)) fun y10 =>
  letN (Nat.xor y00 (fm a y10)) fun w00 => letN (Nat.xor y01 (fm a y11)) fun w01 =>
  letN (fm a' y10) fun w10 => letN (fm a' y11) fun w11 =>
  Nat.add (Nat.xor (fm w00 b1) (fm w01 b))
    (Nat.mul 4 (Nat.add (fm w01 b2) (Nat.mul 4 (Nat.add (Nat.xor (fm w10 b1) (fm w11 b))
      (Nat.mul 4 (fm w11 b2))))))

@[expose] noncomputable def matN (a a' b1 b b2 s t : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k ih => Nat.lor ih
    (Nat.shiftLeft (actN a a' b1 b b2 s t (Nat.shiftLeft 1 k)) (Nat.mul 8 k))) 8

@[expose] noncomputable def IDQ : Nat := 9241421688590303745

@[expose] noncomputable def FULL : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF

@[expose] noncomputable def BP : List Nat :=
  [0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA,
   0xCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCC,
   0xF0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0,
   0xFF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00,
   0xFFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000,
   0xFFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000,
   0xFFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFF0000000000000000,
   0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000]

@[expose] noncomputable def plane (L i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun Bk _ ih k => Nat.xor (Bool.rec (motive := fun _ => Nat) 0 Bk
      (Nat.blt 0 (Nat.land L (Nat.shiftLeft 1 (Nat.add (Nat.mul 8 k) i))))) (ih (Nat.succ k))) BP 0

@[expose] noncomputable def kerMask (L : Nat) : Nat :=
  Nat.sub FULL (Nat.rec (motive := fun _ => Nat) 0 (fun i ih => Nat.lor ih (plane L i)) 8)

@[expose] noncomputable def xlate (M w : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ M => M)
    (fun Bj _ ih j M => ih (Nat.succ j) (Bool.rec (motive := fun _ => Nat) M
      (letN M fun M => letN (Nat.sub FULL Bj) fun lo => Nat.lor
        (Nat.shiftLeft (Nat.land M lo) (Nat.shiftLeft 1 j))
        (Nat.land (Nat.shiftRight M (Nat.shiftLeft 1 j)) lo))
      (Nat.blt 0 (Nat.land w (Nat.shiftLeft 1 j))))) BP 0 M

@[expose] noncomputable def spanAdd (U L : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) U (fun k ih => letN ih fun M =>
    Nat.lor M (xlate M (Nat.land (Nat.shiftRight L (Nat.mul 8 k)) 255))) 8

@[expose] noncomputable def imMask (L : Nat) : Nat := spanAdd 1 L

@[expose] noncomputable def letRec (y : Nat) (k : Nat → List (Nat × (Nat × Nat))) :
    List (Nat × (Nat × Nat)) :=
  Nat.rec (motive := fun _ => List (Nat × (Nat × Nat))) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def invRecsK : List (Nat × (Nat × Nat)) :=
  Nat.rec (motive := fun _ => List (Nat × (Nat × Nat))) [] (fun i ih =>
    letRec (Nat.sub 1727 i) fun j =>
    letRec (matN (Nat.div j 432) (Nat.succ (Nat.mod (Nat.div j 144) 3))
        (Nat.succ (Nat.mod (Nat.div j 48) 3)) (Nat.mod (Nat.div j 12) 4)
        (Nat.succ (Nat.mod (Nat.div j 4) 3)) (Nat.mod (Nat.div j 2) 2) (Nat.mod j 2)) fun M =>
      Bool.rec (motive := fun _ => List (Nat × (Nat × Nat))) ih
        (letRec (Nat.xor M IDQ) fun L => List.cons (L, (kerMask L, imMask L)) ih)
        (Nat.beq (mulF2 8 M M) IDQ)) 1728

@[expose] noncomputable def subB (a b : Nat) : Bool := Nat.beq (Nat.land a b) a

@[expose] noncomputable def memL (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun z _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq x z)) l

@[expose] noncomputable def countK (D : List (Nat × (Nat × Nat))) (W : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun d _ ih => letN ih fun c =>
    Prod.rec (motive := fun _ => Nat) (fun _ fc => Prod.rec (motive := fun _ => Nat)
      (fun fx cm => Bool.rec (motive := fun _ => Nat) c (Nat.succ c)
        (Bool.rec (motive := fun _ => Bool) false (subB cm W) (subB W fx))) fc) d) D

@[expose] noncomputable def popK (W : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun v ih => letN ih fun c =>
    Nat.add c (Nat.land (Nat.shiftRight W v) 1)) 256

@[expose] noncomputable def capStepB (D : List (Nat × (Nat × Nat))) (R : List Nat) (W : Nat) :
    Bool :=
  List.rec (motive := fun _ => Bool) true (fun d _ ih => Prod.rec (motive := fun _ => Bool)
    (fun _ fc => Prod.rec (motive := fun _ => Bool) (fun fx cm =>
      Bool.rec (motive := fun _ => Bool) false ih
        (Bool.rec (motive := fun _ => Bool) true (memL (Nat.land W fx) R) (subB cm W))) fc) d) D

@[expose] noncomputable def plusStepB (D : List (Nat × (Nat × Nat))) (R : List Nat) (U : Nat) :
    Bool :=
  List.rec (motive := fun _ => Bool) true (fun d _ ih => Prod.rec (motive := fun _ => Bool)
    (fun L fc => Prod.rec (motive := fun _ => Bool) (fun fx _ =>
      Bool.rec (motive := fun _ => Bool) false ih
        (Bool.rec (motive := fun _ => Bool) true (memL (spanAdd U L) R) (subB U fx))) fc) d) D

@[expose] noncomputable def allR (R : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun W _ ih => Bool.rec (motive := fun _ => Bool) false ih (f W)) R

@[expose] noncomputable def capOKK (D : List (Nat × (Nat × Nat))) (R : List Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (allR R fun W => Bool.rec (motive := fun _ => Bool) false
      (Nat.ble (Nat.mul (Nat.pow (countK D W) 4) (Nat.pow (popK W) 3)) 16777216)
      (capStepB D R W))
    (memL FULL R)

@[expose] noncomputable def plusOKK (D : List (Nat × (Nat × Nat))) (R : List Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (allR R fun U => Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) (Nat.blt (countK D U) (popK U)) true (Nat.beq U 1))
      (plusStepB D R U))
    (memL 1 R)

@[expose] noncomputable def eqRecs : List (Nat × (Nat × Nat)) → List (Nat × (Nat × Nat)) → Bool :=
  List.rec (motive := fun _ => List (Nat × (Nat × Nat)) → Bool)
    (List.rec (motive := fun _ => Bool) true (fun _ _ _ => false))
    (fun d _ ih E => List.rec (motive := fun _ => Bool) false (fun e E' _ =>
      Prod.rec (motive := fun _ => Bool) (fun L fc => Prod.rec (motive := fun _ => Bool)
        (fun fx cm => Prod.rec (motive := fun _ => Bool) (fun L' fc' =>
          Prod.rec (motive := fun _ => Bool) (fun fx' cm' =>
            Bool.rec (motive := fun _ => Bool) false
              (Bool.rec (motive := fun _ => Bool) false
                (Bool.rec (motive := fun _ => Bool) false (ih E') (Nat.beq cm cm'))
                (Nat.beq fx fx'))
              (Nat.beq L L')) fc') e) fc) d) E)

end CFSG.KC.L34Q
