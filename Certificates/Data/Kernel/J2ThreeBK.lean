module

public import CFSG.Certificates.Kernel.Spor.PackWord
public import Certificates.Data.J2ThreeB

public section

namespace CFSG.KC.J2ThreeBK

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.C89090

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 315 9 (mask 9) p q

@[expose] noncomputable def gen (A B k : Nat) : Nat := Bool.rec B A (Nat.beq k 0)

@[expose] noncomputable def wd (A B : Nat) (w : List Nat) : Nat :=
  wordTabK 315 9 (mask 9) (pidn 315 9) (gen A B) w

@[expose] noncomputable def strictL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def forceL : List Nat → (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun x _ ih k => strictB x fun x' => ih fun r => k (x' :: r))

@[expose] noncomputable def prodsOf (A B y : Nat) (ps : List (List Nat × List Nat)) : List Nat :=
  ps.flatMap fun p => strictL (wd A B p.1) fun a => strictL (wd A B p.2) fun b =>
    [pc a b, pc (pc a y) b, pc (pc a (pc y y)) b]

@[expose] noncomputable def parityK (I : Nat) (T : List Nat) : Bool :=
  T.any (fun t => Nat.beq t I) &&
    T.all fun t => (T.countP fun u => Nat.beq u t) % 2 == if Nat.beq t I then 1 else 0

@[expose] noncomputable def checkAK (A B I : Nat) : Bool :=
  strictB A fun A => strictB B fun B => strictB I fun I => strictB (wd A B y0W) fun y =>
    Nat.beq (pc y (pc y y)) I && forceL (prodsOf A B y pairW) (parityK I)

@[expose] noncomputable def ptK (I Z y : Nat) (C : List Nat) (p : Nat) : Bool :=
  (Nat.beq p I || Nat.beq p Z || Nat.beq p (pc Z Z)) ||
    C.any fun c => Nat.beq (pc c y) (pc p c)

@[expose] noncomputable def checkBK (A B I Z : Nat) (P : Nat → Nat) : Bool :=
  strictB A fun A => strictB B fun B => strictB I fun I => strictB Z fun Z =>
    strictB (wd A B y0W) fun y => forceL (conjW.map (wd A B)) fun C =>
      (List.range 27).all fun j => strictB (P j) fun p => ptK I Z y C p

end CFSG.KC.J2ThreeBK
