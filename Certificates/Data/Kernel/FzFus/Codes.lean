module

public import Certificates.Data.Kernel.FzJt.Codes
public import Certificates.Data.FzFusCls

@[expose] public noncomputable section

namespace Certificates.FzFus.K

open Certificates.FzJt.K

def mul8R (a1 b1 c1 e1 a2 b2 c2 e2 : Nat) : Nat :=
  mk (qm a1 (sw e1 a2 b2)) (qm b1 (sw e1 b2 a2)) (qm c1 c2) (Nat.xor e1 e2)
def mul5R (a1 b1 c1 e1 d : Nat) : Nat :=
  mul8R a1 b1 c1 e1 (Nat.land d 7) (Nat.land (Nat.shiftRight d 3) 7)
    (Nat.land (Nat.shiftRight d 6) 7) (Nat.shiftRight d 9)
def mulR (c d : Nat) : Nat :=
  mul5R (Nat.land c 7) (Nat.land (Nat.shiftRight c 3) 7) (Nat.land (Nat.shiftRight c 6) 7)
    (Nat.shiftRight c 9) d

def lt (x : Nat) : Nat := Nat.add (Nat.land x 1) (Nat.mul 2 (Nat.shiftRight x 2))
def TT : Nat := 548990458703455256239736400950543188581013418660442459642934095276333109462153613769925705334784
def REPT : Nat := 220860097234124997481754757498753492068537512105336813684345155494356041
def CT : Nat := 1521152000

def bEq (a b : Bool) : Bool := Bool.rec (bN b) b a

def clsN (c : Nat) : Nat :=
  Bool.rec
    (Bool.rec (Nat.add 17 (lt (Nat.land (Nat.shiftRight c 6) 7))) 21
      (Nat.beq (lt (Nat.land (Nat.shiftRight c 6) 7)) 0))
    (Bool.rec
      (Bool.rec 22 23
        (bA (bEq (Nat.beq (Nat.land c 7) 2) (Nat.beq (Nat.land (Nat.shiftRight c 3) 7) 2))
          (bN (bEq (Nat.beq (Nat.land (Nat.shiftRight c 6) 7) 2) (Nat.beq (Nat.land c 7) 2)))))
      (Nat.land (Nat.shiftRight TT (Nat.mul 5 (Nat.add (Nat.mul 16 (lt (Nat.land c 7)))
        (Nat.add (Nat.mul 4 (lt (Nat.land (Nat.shiftRight c 3) 7)))
          (lt (Nat.land (Nat.shiftRight c 6) 7)))))) 31)
      (bA (bN (Nat.beq (lt (Nat.land c 7)) 0))
        (bA (bN (Nat.beq (lt (Nat.land (Nat.shiftRight c 3) 7)) 0))
          (bN (Nat.beq (lt (Nat.land (Nat.shiftRight c 6) 7)) 0)))))
    (Nat.beq (Nat.shiftRight c 9) 0)

def repR (k : Nat) : Nat := Nat.land (Nat.shiftRight REPT (Nat.mul 10 k)) 1023
def chiN (n x : Nat) : Nat := Nat.land (Nat.shiftRight CT (Nat.add (Nat.mul 8 n) x)) 1
def phiR (u v c : Nat) : Nat :=
  Nat.xor (Nat.xor (chiN u (Nat.land c 7)) (chiN u (Nat.land (Nat.shiftRight c 3) 7)))
    (chiN v (Nat.land (Nat.shiftRight c 6) 7))

def isInvR (c : Nat) : Bool := bA (Nat.beq (nz (mulR c c)) 0) (bN (Nat.beq (nz c) 0))

def filterN (n : Nat) (p : Nat → Bool) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) []
    (fun i acc => Bool.rec acc (List.cons i acc) (p i)) n
def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => bA (f i) acc) n
def hiL (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun x _ acc => List.cons (Nat.shiftRight x 10) acc) L

def conjOK (x : Nat) : Bool :=
  bA (Nat.blt (Nat.shiftRight x 10) 1024)
    (Nat.beq (nz (mulR (Nat.shiftRight x 10) (Nat.land x 1023)))
      (nz (mulR (repR (clsN (Nat.land x 1023))) (Nat.shiftRight x 10))))
def classB (W : List Nat) : Bool := bA (eqL (filterN 1024 isInvR) (lowL W)) (allL W conjOK)

def clsIdx : Cls → Nat
  | .III => 0 | .IIJ => 1 | .IIK => 2 | .JJI => 3 | .JJJ => 4 | .JJK => 5 | .KKI => 6
  | .KKJ => 7 | .KKK => 8 | .IJI => 9 | .IJJ => 10 | .IJK => 11 | .IKI => 12 | .IKJ => 13
  | .IKK => 14 | .JKI => 15 | .JKJ => 16 | .JKK => 17 | .oI => 18 | .oJ => 19 | .oK => 20
  | .lam => 21 | .z12 => 22 | .z3 => 23

def rowsT : List Nat :=
  rowTable.map fun r => clsIdx r.1 + 32 * clsIdx r.2.1 + 1024 * clsIdx r.2.2

def rowOK (x : Nat) : Bool :=
  bA (Nat.beq (nz (mulR (Nat.land x 1023) (repR (Nat.land (Nat.shiftRight x 10) 31))))
      (nz (mulR (repR (Nat.land (Nat.shiftRight x 10) 31)) (Nat.land x 1023))))
  (bA (isInvR (Nat.land x 1023))
  (bA (bN (Nat.beq (nz (Nat.land x 1023)) (nz (repR (Nat.land (Nat.shiftRight x 10) 31)))))
  (bA (isInvR (mulR (Nat.land x 1023) (repR (Nat.land (Nat.shiftRight x 10) 31))))
  (bA (Nat.beq (clsN (Nat.land x 1023)) (Nat.land (Nat.shiftRight x 15) 31))
    (Nat.beq (clsN (mulR (Nat.land x 1023) (repR (Nat.land (Nat.shiftRight x 10) 31))))
      (Nat.shiftRight x 20))))))
def rowsB (T W : List Nat) : Bool := bA (eqL (hiL W) T) (allL W rowOK)

def subsT : List (List Nat) :=
  subTable.map fun s => s.1.val :: s.2.1.val :: s.2.2.map clsIdx

def subOK (α β : Nat) (L : List Nat) : Bool :=
  allN 1024 fun c => bI (isInvR c) (bI (Nat.beq (phiR α β c) 0) (memL (clsN c) L))
def subRow (r : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun α t _ => List.rec (motive := fun _ => Bool) false (fun β L _ => subOK α β L) t) r
def subsB (S : List (List Nat)) : Bool := allRows S subRow

def pA (a : Nat) : Bool := bN (bO (Nat.beq (mulK a a) 0) (Nat.beq (mulK a a) 18))
def d5K (a b : Nat) : Bool :=
  bA (commK a b)
  (bA (bN (Nat.beq (mulK (mulK a a) (mulK b b)) 0))
  (bA (bN (Nat.beq (mulK (mulK a a) (mulK b b)) 18))
  (bA (bN (Nat.beq (mulK a a) (mulK b b)))
  (bA (bN (Nat.beq (mulK (mulK a a) (mulK b b)) (mulK a a)))
    (bN (Nat.beq (mulK (mulK a a) (mulK b b)) (mulK b b)))))))
def conjP (P : List Nat) (x : Nat) : Bool :=
  bA (isC (Nat.land (Nat.shiftRight x 10) 1023))
  (bA (isC (Nat.shiftRight x 20))
  (bA (memL (Nat.shiftRight x 20) P)
    (Nat.beq (mulK (Nat.land (Nat.shiftRight x 10) 1023) (Nat.land x 1023))
      (mulK (Nat.shiftRight x 20) (Nat.land (Nat.shiftRight x 10) 1023)))))
def p7B (A P X : List Nat) : Bool :=
  bA (eqL (filterR 512 pA) A)
  (bA (eqL (lowL X) A)
  (bA (allL X (conjP P))
    (allL P fun a => allL A fun b => bN (d5K a b))))

end Certificates.FzFus.K
