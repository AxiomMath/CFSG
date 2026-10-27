module

public import Certificates.Data.Kernel.Spor.Fi24Kit
public import Certificates.Data.Kernel.Spor.Fi24ThreeO
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.Fi24R2W

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeO

@[expose] noncomputable def walkN (NW : Nat → Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun l _ ih x => strictN (letN NW l x) ih) w x

@[expose] def invC (w : List Nat) : List Nat := (w.map fun l => Nat.xor l 1).reverse

@[expose] def hwS (A B : List Nat) (w : List Nat) : List Nat :=
  (w.map fun x => if x = 0 then A else B).flatten

@[expose] def H0 : List Nat := (List.replicate 30
  [11, 25, 14, 12, 8, 4, 10, 24, 11, 8, 23, 24, 12, 5, 23, 20, 18, 11, 5, 24]).flatten

@[expose] def H1 : List Nat :=
  [19, 11, 15, 6, 13, 14, 12, 5, 15, 14, 17, 22, 20, 8, 19, 24, 5, 10, 21, 11] ++
    (List.replicate 4
      [19, 20, 24, 22, 13, 7, 22, 9, 17, 5, 15, 6, 5, 15, 18, 14, 25, 24, 10, 20]).flatten ++
    [10, 20, 11, 4, 25, 18, 9, 21, 23, 16, 15, 14, 4, 13, 15, 12, 7, 14, 10, 18]

@[expose] def S0 : List Nat := [7, 4, 16, 25, 6, 14, 11, 16, 20, 8, 14, 14, 25, 17, 14, 17, 22, 17]

@[expose] def S1 : List Nat :=
  [14, 17, 4, 23, 5, 21, 9, 20, 17, 8, 16, 24, 15, 19, 14, 12, 22, 25, 16, 24]

@[expose] def SD1 : List Nat :=
  [8, 25, 5, 23, 7, 4, 8, 21, 10, 8, 8, 19, 20, 15, 15, 24, 14, 17, 21, 23, 25]

@[expose] def SD : List Nat :=
  [13, 21, 5, 11, 20, 4, 23, 20, 9, 10, 10, 8, 15, 23, 14, 16, 13, 14, 22, 19, 17, 24]

@[expose] def SU2 : List Nat :=
  [5, 25, 15, 9, 7, 11, 20, 8, 18, 11, 8, 16, 23, 15, 21, 16, 14, 18, 21, 23, 18, 24]

@[expose] def SW : List Nat :=
  [17, 21, 5, 18, 5, 12, 11, 15, 18, 8, 8, 19, 12, 14, 20, 14, 13, 18, 23, 17, 24]

@[expose] def SR : List Nat := [8, 19, 6, 6, 8, 15, 23, 10, 10, 8, 12, 24, 21, 14, 20, 23, 20, 16, 25]

@[expose] def dWL : List Nat := [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1]

@[expose] def wWL : List Nat := [1, 1, 0, 1, 1, 0, 1]

@[expose] def BA : List Nat := [23, 4, 1, 2, 9, 22, 13, 4]

@[expose] def BB : List Nat := [13, 5, 14, 25, 18, 1, 18, 18]

@[expose] def bray (g : List Nat) (e : Nat) : List Nat :=
  g ++ (List.replicate e (SR ++ (invC g ++ (SR ++ g)))).flatten

@[expose] def SA : List Nat :=
  [0, 5, 21, 9, 2, 12, 23, 7, 21, 7, 19, 11, 15, 23, 8, 14, 12, 15, 15, 21, 12, 23, 24, 16, 25]

@[expose] def SB : List Nat :=
  [14, 11, 15, 6, 0, 20, 7, 11, 4, 6, 8, 16, 13, 17, 14, 8, 13, 14, 12, 14, 23, 14, 21, 24, 16, 24]

@[expose] def base : List Nat := [0, 305530, 5604, 221549, 266275, 186844]

@[expose] noncomputable def stageOK (NW : Nat → Nat → Nat) (X Y : List Nat) : Bool :=
  base.all fun b => Nat.beq (walkN NW X.reverse b) (walkN NW Y.reverse b)

@[expose] noncomputable def fpt (F j : Nat) : Nat := CFSG.KC.Enum.pg 19 (CFSG.KS.mask 19) F j

@[expose] noncomputable def krow (K j : Nat) : Nat := CFSG.KC.Enum.pg 9 (CFSG.KS.mask 9) K j

@[expose] noncomputable def selP (F : Nat) (f : Nat → Nat) (b : Nat) : List Nat :=
  ((List.range 504).filter fun i => Nat.beq b 9 || Nat.testBit (f i) b).map (fpt F)

@[expose] noncomputable def plOK (NW : Nat → Nat → Nat) (c : List Nat) (F : Nat) (f : Nat → Nat) :
    Bool :=
  CFSG.KC.Enum.allN 10 fun b => Nat.beq (walkP NW c (plOf (selP F (fun i => i) b))) (plOf (selP F f b))

end CFSG.KC.Fi24R2W

end
